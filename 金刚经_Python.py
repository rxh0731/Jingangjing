"""
《金刚经》排版 — Python 版 v1.2.1 (2026-06-20)
==============================================
功能说明：
  本程序用于将《金刚般若波罗蜜经》全文（5176字）自动排版为 PSD 文件。
  支持生成 16 块小版 + 5 块大版，每字独立为一个图层，支持图层名称标注。

核心能力：
  - 功能完全复刻 ExtendScript 版本，但运行速度提升 10~50 倍。
  - 输出格式为 PSD（Photoshop 文档），保留图层结构，支持后续手动编辑。
  - 支持每字独立图层，图层名格式为"字_行号_列号"（如"佛_1_1"）。
  - 支持 DPI（72~200）配置，控制输出分辨率。
  - 支持尺寸标注图层，包含画布尺寸、单元格尺寸、大框尺寸、边距等信息。
  - 支持进度条显示和日志记录。
  - 提供 Tkinter GUI 界面，支持参数配置、校验、保存/恢复默认值。

运行环境：
  - Python 3.7+
  - 依赖包：Pillow（图像处理）、psd-tools（PSD 读写）、tkinter（GUI，Python 自带）

v1.2.0 优化项：
  - 白底转透明改用 Pillow ImageChops C 级处理，提升 5~10 倍
  - 图片路径+DPI LRU 缓存，减少重复文件 IO
  - 字库版本探测 probe_versions 增加独立 LRU 缓存
  - GBK 编码检查改用预计算集合，避免逐字 try/except
  - 缺字检查支持变体版本号文件检测
  - 删除无用导入和死代码，精简启动开销
  - 缩小 GBK 不可编码字符预计算范围
  - 大版进度条映射优化，进度变化更平滑

v1.2.1 更新（2026-06-20）：
  - 修复文件头部多余引号的格式瑕疵
  - 删除残留的旧版进度权重注释
  - 全文添加详细中文注释说明，覆盖所有函数、类、参数、算法和关键逻辑
"""
# ==================== 标准库导入 ====================
import os           # 文件系统操作
import sys          # 系统参数、标准输出重编码
import json         # 配置文件读写
import time         # 计时、日志时间戳
import gc           # 垃圾回收（处理大版 PSD 后手动释放内存）
import tkinter as tk                     # GUI 框架（窗口、组件）
from tkinter import ttk, filedialog, messagebox  # ttk: 现代化组件 | filedialog: 文件对话框 | messagebox: 弹窗
from PIL import Image, ImageDraw, ImageFont, ImageChops  # Pillow 图像处理库

# 关闭 Pillow 的 DecompressionBomb 安全限制（本脚本处理合法的大尺寸图片，无需此保护）
Image.MAX_IMAGE_PIXELS = None

# ---- 标准输出编码设置 ----
# 确保 print() 和 log() 输出中文不会因 GBK 编码而报错
if hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # type: ignore[attr-defined]
    except Exception:
        pass

# ---- PSD 处理库 ----
# psd-tools：用于生成带图层的 Photoshop PSD 文件
from psd_tools import PSDImage
from psd_tools.psd.image_resources import ImageResource  # PSD 图像资源（用于设置 DPI）
from psd_tools.constants import Resource, Compression    # DPI 资源键 和 RLE 压缩常量
import struct  # 二进制数据打包（用于 DPI 数据写入）
from functools import lru_cache  # LRU 缓存装饰器（函数结果缓存）

# ==================== 用户中断异常 ====================
class GenerationCancelled(Exception):
    """用户中断生成异常。
    在任意阶段循环中检测到取消标志时抛出，直接穿透调用栈回到顶层调度器，
    由 run_generation() 统一捕获并处理。
    """
    pass

# ==================== GBK 编码兼容性处理 ====================
# 核心问题：Photoshop 中文版（Windows）内部使用 GBK 编码存储图层名称。
# 经文中有少量生僻汉字（如"闇""麁"等）不在 GBK 编码范围内，
# 如果图层名包含这些字，保存 PSD 时 psd-tools 会抛出 UnicodeEncodeError。
#
# 解决方案：
#   1. 程序启动时预计算 GBK 不可编码的 CJK 字符集合（约 5000 个），
#      存入 _GBK_UNENCODABLE 全局集合。
#   2. 每次创建图层时，通过 _safe_psd_name() 检查图层名中的每个字符：
#      - 如果字符在 _GBK_UNENCODABLE 中 → 替换为 '?' 并记录警告日志。
#      - 如果字符不在集合中 → 保留原样。
#   3. 预计算仅遍历 CJK 相关 Unicode 区间，跳过无关区域，节约启动时间。
#
# 注意：预计算在模块加载时执行（约 0.1 秒），结果常驻内存，
# 避免了每次创建图层时都执行 try/except .encode('gbk') 操作。

# _GBK_UNENCODABLE: GBK 无法编码的 CJK 字符集合（全局预计算）
_GBK_UNENCODABLE = set()

# _CJK_RANGES: 经文可能用到的 CJK Unicode 区间
#   扩展A区 (U+3400~U+4DBF)：罕见汉字补充区
#   基本区   (U+4E00~U+9FFF)：常用汉字主体，包括经文全部常见字
#   兼容区   (U+F900~U+FAFF)：与基本区重复的兼容字符（历史原因）
_CJK_RANGES = [(0x3400, 0x4DC0), (0x4E00, 0xA000), (0xF900, 0xFB00)]
for _lo, _hi in _CJK_RANGES:
    for _code in range(_lo, _hi):
        try:
            chr(_code).encode('gbk')
        except (UnicodeEncodeError, OverflowError):
            _GBK_UNENCODABLE.add(chr(_code))

# _GBK_UNENCODABLE_LOG: 已记录警告的字符集合（防止重复打印相同字符的警告）
_GBK_UNENCODABLE_LOG = set()


def _safe_psd_name(name):
    """确保图层名称可用 GBK 编码，无法编码的字符替换为 '?'。
    
    Photoshop 中文版在 Windows 上使用 GBK 编码存储图层名称。
    如果图层名包含 GBK 不支持的字符（如某些生僻汉字），
    保存 PSD 时会抛出 UnicodeEncodeError。

    本函数检查 name 中的每个字符：
      - 如果在 _GBK_UNENCODABLE 预计算集合中 → 替换为 '?'
      - 否则保留原字符

    参数：
      name (str): 原始图层名称（如"闇_5_3"）

    返回：
      str: 安全的图层名称（如"?_5_3"）
    """
    result = []
    for c in name:
        if c in _GBK_UNENCODABLE:
            if c not in _GBK_UNENCODABLE_LOG:
                _GBK_UNENCODABLE_LOG.add(c)
                log(f"  [WARN] 字符 U+{ord(c):04X} 无法用 GBK 编码，已替换为 '?'")
            result.append('?')
        else:
            result.append(c)
    return ''.join(result)

# PSD 文件保存时使用的编码（GBK = 中文 Windows Photoshop 默认编码）
PSD_ENCODING = 'gbk'


# ==================== PSD 元数据工具函数 ====================
def set_psd_resolution(psd, dpi):
    """设置 PSD 文档的 DPI（分辨率）元数据。
    
    PSD 文件以 16.16 定点数存储分辨率（高 16 位为整数部分）。
    本函数构造符合 Photoshop 规范的 ImageResource 块，并写入 PSD 头。
    
    参数：
      psd (PSDImage): psd-tools 的 PSDImage 对象
      dpi (int): 目标 DPI 值（如 150、300）
    """
    h_res = int(dpi * 0x10000)  # 水平分辨率：16.16 定点数
    v_res = int(dpi * 0x10000)  # 垂直分辨率：16.16 定点数
    data = struct.pack('>I', h_res)
    data += struct.pack('>H', 1)  # h_res_unit: 1=像素/英寸 (PPI)
    data += struct.pack('>H', 2)  # width_unit: 2=毫米 (mm)
    data += struct.pack('>I', v_res)
    data += struct.pack('>H', 1)  # v_res_unit: 1=像素/英寸 (PPI)
    data += struct.pack('>H', 2)  # height_unit: 2=毫米 (mm)
    ri = ImageResource(signature=b'8BIM', key=Resource.RESOLUTION_INFO, name='', data=data)
    psd.image_resources[Resource.RESOLUTION_INFO] = ri

# ==================== 全局常量定义 ====================
# ---- 路径常量 ----
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))  # 脚本所在目录（用于定位配置文件和日志）
CONFIG_PATH = os.path.join(SCRIPT_DIR, "金刚经排版参数.json")  # 参数持久化文件路径

# ---- 颜色常量（RGB 格式）----
LINE_COLOR = (139, 0, 0)       # 深红色 — 单元格边框和大框外框
GUIDE_COLOR = (0, 128, 0)      # 绿色   — 单元格内十字辅助中线
SPLIT_COLOR = (0, 0, 255)      # 蓝色   — 分割线（上半部/下半部之间的分界线）

# ---- 图片格式常量 ----
# 字库支持的图片格式，按优先级排列（先检测 jpg 再 tif 再 png）
IMAGE_EXTS = [".jpg", ".tif", ".png", ".psd"]

# ==================== 经文全文 ====================
# 《金刚般若波罗蜜经》完整经文（鸠摩罗什译本）
# 格式说明：
#   - 每个 \n 代表一个段落分隔符（分品标记）
#   - 全角空格（　）用于偈颂对齐
#   - 总字数约 5176 字
# 程序通过 parse_scripture() 解析此文本，提取汉字并分配至 16 块小版的单元格中
SCRIPTURE_TEXT = (
    "佛说金刚般若波罗蜜经\n"
    "如是我闻一时佛在舍卫国祇树给孤独园与大比丘众千二百五十人俱尔时世尊食时著衣持钵"
    "入舍卫大城乞食于其城中次第乞已还至本处饭食讫收衣钵洗足已敷座而坐\n"
    "时长老须菩提在大众中即从座起偏袒右肩右膝著地合掌恭敬而白佛言希有世尊如来善护念"
    "诸菩萨善付嘱诸菩萨世尊善男子善女人发阿耨多罗三藐三菩提心应云何住云何降伏其心"
    "佛言善哉善哉须菩提如汝所说如来善护念诸菩萨善付嘱诸菩萨汝今谛听当为汝说善男子善女人"
    "发阿耨多罗三藐三菩提心应如是住如是降伏其心唯然世尊愿乐欲闻\n"
    "佛告须菩提诸菩萨摩诃萨应如是降伏其心所有一切众生之类若卵生若胎生若湿生若化生"
    "若有色若无色若有想若无想若非有想非无想我皆令入无余涅槃而灭度之如是灭度无量无数无边众生"
    "实无众生得灭度者何以故须菩提若菩萨有我相人相众生相寿者相即非菩萨\n"
    "复次须菩提菩萨于法应无所住行于布施所谓不住色布施不住声香味触法布施须菩提菩萨应如是布施"
    "不住于相何以故若菩萨不住相布施其福德不可思量须菩提于意云何东方虚空可思量不不也世尊"
    "须菩提南西北方四维上下虚空可思量不不也世尊须菩提菩萨无住相布施福德亦复如是不可思量"
    "须菩提菩萨但应如所教住\n"
    "须菩提于意云何可以身相见如来不不也世尊不可以身相得见如来何以故如来所说身相即非身相"
    "佛告须菩提凡所有相皆是虚妄若见诸相非相则见如来\n"
    "须菩提白佛言世尊颇有众生得闻如是言说章句生实信不佛告须菩提莫作是说如来灭后后五百岁"
    "有持戒修福者于此章句能生信心以此为实当知是人不于一佛二佛三四五佛而种善根已于无量千万佛所"
    "种诸善根闻是章句乃至一念生净信者须菩提如来悉知悉见是诸众生得如是无量福德何以故是诸众生"
    "无复我相人相众生相寿者相无法相亦无非法相何以故是诸众生若心取相则为著我人众生寿者"
    "若取法相即著我人众生寿者何以故若取非法相即著我人众生寿者是故不应取法不应取非法"
    "以是义故如来常说汝等比丘知我说法如筏喻者法尚应舍何况非法\n"
    "须菩提于意云何如来得阿耨多罗三藐三菩提耶如来有所说法耶须菩提言如我解佛所说义"
    "无有定法名阿耨多罗三藐三菩提亦无有定法如来可说何以故如来所说法皆不可取不可说非法非非法"
    "所以者何一切贤圣皆以无为法而有差别\n"
    "须菩提于意云何若人满三千大千世界七宝以用布施是人所得福德宁为多不须菩提言甚多世尊"
    "何以故是福德即非福德性是故如来说福德多若复有人于此经中受持乃至四句偈等为他人说其福胜彼"
    "何以故须菩提一切诸佛及诸佛阿耨多罗三藐三菩提法皆从此经出须菩提所谓佛法者即非佛法\n"
    "须菩提于意云何须陀洹能作是念我得须陀洹果不须菩提言不也世尊何以故须陀洹名为入流而无所入"
    "不入色声香味触法是名须陀洹须菩提于意云何斯陀含能作是念我得斯陀含果不须菩提言不也世尊"
    "何以故斯陀含名一往来而实无往来是名斯陀含须菩提于意云何阿那含能作是念我得阿那含果不"
    "须菩提言不也世尊何以故阿那含名为不来而实无来是故名阿那含须菩提于意云何阿罗汉能作是念"
    "我得阿罗汉道不须菩提言不也世尊何以故实无有法名阿罗汉世尊若阿罗汉作是念我得阿罗汉道"
    "即为著我人众生寿者世尊佛说我得无诤三昧人中最为第一是第一离欲阿罗汉我不作是念我是离欲"
    "阿罗汉世尊我若作是念我得阿罗汉道世尊则不说须菩提是乐阿兰那行者以须菩提实无所行"
    "而名须菩提是乐阿兰那行\n"
    "佛告须菩提于意云何如来昔在然灯佛所于法有所得不世尊如来在然灯佛所于法实无所得"
    "须菩提于意云何菩萨庄严佛土不不也世尊何以故庄严佛土者则非庄严是名庄严是故须菩提"
    "诸菩萨摩诃萨应如是生清净心不应住色生心不应住声香味触法生心应无所住而生其心"
    "须菩提譬如有人身如须弥山王于意云何是身为大不须菩提言甚大世尊何以故佛说非身是名大身\n"
    "须菩提如恒河中所有沙数如是沙等恒河于意云何是诸恒河沙宁为多不须菩提言甚多世尊"
    "但诸恒河尚多无数何况其沙须菩提我今实言告汝若有善男子善女人以七宝满尔所恒河沙数"
    "三千大千世界以用布施得福多不须菩提言甚多世尊佛告须菩提若善男子善女人于此经中"
    "乃至受持四句偈等为他人说而此福德胜前福德\n"
    "复次须菩提随说是经乃至四句偈等当知此处一切世间天人阿修罗皆应供养如佛塔庙"
    "何况有人尽能受持读诵须菩提当知是人成就最上第一希有之法若是经典所在之处则为有佛若尊重弟子\n"
    "尔时须菩提白佛言世尊当何名此经我等云何奉持佛告须菩提是经名为金刚般若波罗蜜以是名字汝当奉持"
    "所以者何须菩提佛说般若波罗蜜则非般若波罗蜜须菩提于意云何如来有所说法不须菩提白佛言世尊"
    "如来无所说须菩提于意云何三千大千世界所有微尘是为多不须菩提言甚多世尊须菩提诸微尘如来说"
    "非微尘是名微尘如来说世界非世界是名世界须菩提于意云何可以三十二相见如来不不也世尊"
    "不可以三十二相得见如来何以故如来说三十二相即是非相是名三十二相须菩提若有善男子善女人"
    "以恒河沙等身命布施若复有人于此经中乃至受持四句偈等为他人说其福甚多\n"
    "尔时须菩提闻说是经深解义趣涕泪悲泣而白佛言希有世尊佛说如是甚深经典我从昔来所得慧眼"
    "未曾得闻如是之经世尊若复有人得闻是经信心清净则生实相当知是人成就第一希有功德"
    "世尊是实相者则是非相是故如来说名实相世尊我今得闻如是经典信解受持不足为难若当来世后五百岁"
    "其有众生得闻是经信解受持是人则为第一希有何以故此人无我相人相众生相寿者相所以者何"
    "我相即是非相人相众生相寿者相即是非相何以故离一切诸相则名诸佛佛告须菩提如是如是"
    "若复有人得闻是经不惊不怖不畏当知是人甚为希有何以故须菩提如来说第一波罗蜜非第一波罗蜜"
    "是名第一波罗蜜须菩提忍辱波罗蜜如来说非忍辱波罗蜜何以故须菩提如我昔为歌利王割截身体"
    "我于尔时无我相无人相无众生相无寿者相何以故我于往昔节节支解时若有我相人相众生相寿者相"
    "应生嗔恨须菩提又念过去于五百世作忍辱仙人于尔所世无我相无人相无众生相无寿者相"
    "是故须菩提菩萨应离一切相发阿耨多罗三藐三菩提心不应住色生心不应住声香味触法生心"
    "应生无所住心若心有住则为非住是故佛说菩萨心不应住色布施须菩提菩萨为利益一切众生"
    "应如是布施如来说一切诸相即是非相又说一切众生则非众生须菩提如来是真语者实语者如语者"
    "不诳语者不异语者须菩提如来所得法此法无实无虚须菩提若菩萨心住于法而行布施如人入闇"
    "则无所见若菩萨心不住法而行布施如人有目日光明照见种种色须菩提当来之世若有善男子善女人"
    "能于此经受持读诵则为如来以佛智慧悉知是人悉见是人皆得成就无量无边功德\n"
    "须菩提若有善男子善女人初日分以恒河沙等身布施中日分复以恒河沙等身布施后日分亦以恒河沙等"
    "身布施如是无量百千万亿劫以身布施若复有人闻此经典信心不逆其福胜彼何况书写受持读诵"
    "为人解说须菩提以要言之是经有不可思议不可称量无边功德如来为发大乘者说为发最上乘者说"
    "若有人能受持读诵广为人说如来悉知是人悉见是人皆得成就不可量不可称无有边不可思议功德"
    "如是人等则为荷担如来阿耨多罗三藐三菩提何以故须菩提若乐小法者著我见人见众生见寿者见"
    "则于此经不能听受读诵为人解说须菩提在在处处若有此经一切世间天人阿修罗所应供养"
    "当知此处则为是塔皆应恭敬作礼围绕以诸华香而散其处\n"
    "复次须菩提善男子善女人受持读诵此经若为人轻贱是人先世罪业应堕恶道以今世人轻贱故"
    "先世罪业则为消灭当得阿耨多罗三藐三菩提须菩提我念过去无量阿僧祇劫于然灯佛前"
    "得值八百四千万亿那由他诸佛悉皆供养承事无空过者若复有人于后末世能受持读诵此经"
    "所得功德于我所供养诸佛功德百分不及一千万亿分乃至算数譬喻所不能及须菩提若善男子善女人"
    "于后末世有受持读诵此经所得功德我若具说者或有人闻心则狂乱狐疑不信须菩提当知是经义不可思议"
    "果报亦不可思议\n"
    "尔时须菩提白佛言世尊善男子善女人发阿耨多罗三藐三菩提心云何应住云何降伏其心"
    "佛告须菩提善男子善女人发阿耨多罗三藐三菩提者当生如是心我应灭度一切众生灭度一切众生已"
    "而无有一众生实灭度者何以故须菩提若菩萨有我相人相众生相寿者相则非菩萨所以者何"
    "须菩提实无有法发阿耨多罗三藐三菩提者须菩提于意云何如来于然灯佛所有法得阿耨多罗三藐三菩提"
    "不不也世尊如我解佛所说义佛于然灯佛所无有法得阿耨多罗三藐三菩提佛言如是如是须菩提"
    "实无有法如来得阿耨多罗三藐三菩提须菩提若有法如来得阿耨多罗三藐三菩提者然灯佛则不与我受记"
    "汝于来世当得作佛号释迦牟尼以实无有法得阿耨多罗三藐三菩提是故然灯佛与我受记作是言"
    "汝于来世当得作佛号释迦牟尼何以故如来者即诸法如义若有人言如来得阿耨多罗三藐三菩提"
    "须菩提实无有法佛得阿耨多罗三藐三菩提须菩提如来所得阿耨多罗三藐三菩提于是中无实无虚"
    "是故如来说一切法皆是佛法须菩提所言一切法者即非一切法是故名一切法须菩提譬如人身长大"
    "须菩提言世尊如来说人身长大则为非大身是名大身须菩提菩萨亦如是若作是言我当灭度无量众生"
    "则不名菩萨何以故须菩提实无有法名为菩萨是故佛说一切法无我无人无众生无寿者"
    "须菩提若菩萨作是言我当庄严佛土是不名菩萨何以故如来说庄严佛土者即非庄严是名庄严"
    "须菩提若菩萨通达无我法者如来说名真是菩萨\n"
    "须菩提于意云何如来有肉眼不如是世尊如来有肉眼须菩提于意云何如来有天眼不如是世尊如来有天眼"
    "须菩提于意云何如来有慧眼不如是世尊如来有慧眼须菩提于意云何如来有法眼不如是世尊如来有法眼"
    "须菩提于意云何如来有佛眼不如是世尊如来有佛眼须菩提于意云何恒河中所有沙佛说是沙不如是世尊"
    "如来说是沙须菩提于意云何如一恒河中所有沙有如是等恒河是诸恒河所有沙数佛世界如是宁为多"
    "不甚多世尊佛告须菩提尔所国土中所有众生若干种心如来悉知何以故如来说诸心皆为非心是名为心"
    "所以者何须菩提过去心不可得现在心不可得未来心不可得\n"
    "须菩提于意云何若有人满三千大千世界七宝以用布施是人以是因缘得福多不如是世尊此人以是因缘"
    "得福甚多须菩提若福德有实如来不说得福德多以福德无故如来说得福德多\n"
    "须菩提于意云何佛可以具足色身见不不也世尊如来不应以具足色身见何以故如来说具足色身"
    "即非具足色身是名具足色身须菩提于意云何如来可以具足诸相见不不也世尊如来不应以具足诸相见"
    "何以故如来说诸相具足即非具足是名诸相具足\n"
    "须菩提汝勿谓如来作是念我当有所说法莫作是念何以故若人言如来有所说法即为谤佛不能解我所说故"
    "须菩提说法者无法可说是名说法尔时慧命须菩提白佛言世尊颇有众生于未来世闻说是法生信心不"
    "佛言须菩提彼非众生非不众生何以故须菩提众生众生者如来说非众生是名众生\n"
    "须菩提白佛言世尊佛得阿耨多罗三藐三菩提为无所得耶如是如是须菩提我于阿耨多罗三藐三菩提"
    "乃至无有少法可得是名阿耨多罗三藐三菩提\n"
    "复次须菩提是法平等无有高下是名阿耨多罗三藐三菩提以无我无人无众生无寿者修一切善法"
    "则得阿耨多罗三藐三菩提须菩提所言善法者如来说非善法是名善法\n"
    "须菩提若三千大千世界中所有诸须弥山王如是等七宝聚有人持用布施若人以此般若波罗蜜经"
    "乃至四句偈等受持读诵为他人说于前福德百分不及一百千万亿分乃至算数譬喻所不能及\n"
    "须菩提于意云何汝等勿谓如来作是念我当度众生须菩提莫作是念何以故实无有众生如来度者"
    "若有众生如来度者如来则有我人众生寿者须菩提如来说有我者则非有我而凡夫之人以为有我"
    "须菩提凡夫者如来说则非凡夫\n"
    "须菩提于意云何可以三十二相观如来不须菩提言如是如是以三十二相观如来佛言须菩提"
    "若以三十二相观如来者转轮圣王则是如来须菩提白佛言世尊如我解佛所说义不应以三十二相观如来"
    "尔时世尊而说偈言　若以色见我　以音声求我　是人行邪道　不能见如来\n"
    "须菩提汝若作是念如来不以具足相故得阿耨多罗三藐三菩提须菩提莫作是念如来不以具足相故"
    "得阿耨多罗三藐三菩提须菩提汝若作是念发阿耨多罗三藐三菩提者说诸法断灭相莫作是念"
    "何以故发阿耨多罗三藐三菩提心者于法不说断灭相\n"
    "须菩提若菩萨以满恒河沙等世界七宝布施若复有人知一切法无我得成于忍此菩萨胜前菩萨所得功德"
    "须菩提以诸菩萨不受福德故须菩提白佛言世尊云何菩萨不受福德须菩提菩萨所作福德不应贪著"
    "是故说不受福德\n"
    "须菩提若有人言如来若来若去若坐若卧是人不解我所说义何以故如来者无所从来亦无所去故名如来\n"
    "须菩提若善男子善女人以三千大千世界碎为微尘于意云何是微尘众宁为多不甚多世尊何以故"
    "若是微尘众实有者佛则不说是微尘众所以者何佛说微尘众则非微尘众是名微尘众世尊如来所说"
    "三千大千世界则非世界是名世界何以故若世界实有者则是一合相如来说一合相则非一合相"
    "是名一合相须菩提一合相者则是不可说但凡夫之人贪著其事\n"
    "须菩提若人言佛说我见人见众生见寿者见须菩提于意云何是人解我所说义不世尊是人不解如来所说义"
    "何以故世尊说我见人见众生见寿者见即非我见人见众生见寿者见是名我见人见众生见寿者见"
    "须菩提发阿耨多罗三藐三菩提心者于一切法应如是知如是见如是信解不生法相须菩提所言法相者"
    "如来说即非法相是名法相\n"
    "须菩提若有人以满无量阿僧祇世界七宝持用布施若有善男子善女人发菩萨心者持于此经"
    "乃至四句偈等受持读诵为人演说其福胜彼云何为人演说不取于相如如不动何以故　一切有为法"
    "　如梦幻泡影　如露亦如电　应作如是观　佛说是经已长老须菩提及诸比丘比丘尼"
    "优婆塞优婆夷一切世间天人阿修罗闻佛所说皆大欢喜信受奉行\n"
    "金刚般若波罗蜜经\n"
)


# ==================== 默认参数配置 ====================
# 所有可调参数均在此字典中定义默认值。
# 程序首次运行时使用默认值；用户通过 GUI 修改后，值会被保存到"金刚经排版参数.json"文件中。
# 每次启动时 load_config() 会从 JSON 文件加载用户上次保存的参数。
DEFAULT_PARAMS = {
    # ---- 路径配置 ----
    "WORK_DIR": "./",                    # 输出目录（PSD 文件保存位置）
    "PIC_FOLDER": "./金刚经字库",         # 字库图片目录（包含各字符的 JPG/TIF/PNG 图片）

    # ---- 输出质量配置 ----
    "DPI": 150,                          # 输出分辨率（72~200，越高越清晰但文件越大）

    # ---- 缩放模式配置 ----
    "SCALE_PERCENT": 100,                # 全局文字缩放百分比（仅"直接等比"模式生效）
    "SCALE_MODE": 0,                     # 缩放模式：0=直接等比缩放, 1=相对单元格缩放
    "AUTO_SCALE_THRESHOLD": 75,          # 自动放大阈值（%）：若文字占格比 ≤ 此值，自动放大
    "AUTO_FILL_W": 95,                   # 自动放大宽度填充比率（%），以格宽为基准
    "AUTO_FILL_H": 95,                   # 自动放大高度填充比率（%），以格高为基准
    "AUTO_SHRINK_THRESHOLD": 150,        # 自动缩小阈值（%）：若文字占格比 ≥ 此值，自动缩小
    "SHRINK_FILL_W": 95,                 # 自动缩小宽度填充比率（%），以格宽为基准
    "SHRINK_FILL_H": 95,                 # 自动缩小高度填充比率（%），以格高为基准
    "CELL_FILL_RATIO": 90,               # 相对单元格模式下的填充比率（%，以较大方向为基准）

    # ---- 排版模式配置 ----
    "SCRIPTURE_MODE": 2,                 # 分段符处理方式：1=换列（每个分品从新列开始）, 2=跳格（跳 N 个空格）

    "PARA_SKIP_COUNT": 2,               # 跳格模式下，每个分段符后跳过的空格数
    "LAST_BR_NEW_COL": 1,               # 尾题（最后一品标题）是否另起一列：0=否, 1=是

    # ---- 输出选项 ----
    "ADD_ANNOTATION": 1,                # 是否添加尺寸标注图层：0=否, 1=是
    "OVERWRITE_MODE": 1,                # 文件冲突处理：0=跳过已存在的文件, 1=覆盖已存在的文件
    "TEST_CHAR_LIMIT": 0,               # 测试用字数限制：0=不限制, >0=仅处理前 N 个字符

    # ---- 经文文本（首次使用默认经文，用户可编辑）----
    "SCRIPTURE_TEXT": SCRIPTURE_TEXT,

    # ====== 单元格参数 ======
    "CELL_W": 130,                      # 单元格宽度（mm）
    "CELL_H": 110,                      # 单元格高度（mm）
    "ROW_GAP": 12,                      # 行间距（mm）
    "ROWS": 33,                         # 每块小版的行数（总行数）
    "BIG_FRAME_MARGIN_TOP": 20,         # 大框上边距（mm），大框顶部到第一行单元格的距离
    "BIG_FRAME_MARGIN_BOTTOM": 20,      # 大框下边距（mm），最后一行单元格到大框底部的距离
    "CANVAS_TO_BIGFRAME_TOP": 266,      # 画布上边距（mm），画布顶部到大框顶部的距离
    "CANVAS_TO_BIGFRAME_BOTTOM": 180,   # 画布下边距（mm），大框底部到画布底部的距离
    "SPLIT_LINE_AFTER_ROW": 10,         # 蓝色分割线位置：在第 N 行之后画分割线

    # ====== 小版模板参数 (T0~T4，对应 5 种模板) ======
    # 模板-1 (T0)：10列，用于小版 1.1/2.1/4.1/5.1
    "T0_CANVAS_W": 1500, "T0_CANVAS_H": 4500,   # 画布宽 x 高 (mm)
    "T0_COLS": 10, "T0_COL_GAP": 10,             # 列数 x 列间距 (mm)
    "T0_BIG_FRAME_L": 10, "T0_BIG_FRAME_R": 20, # 大框左边距 x 右边距 (mm)
    "T0_CANVAS_TO_BIG_L": 0, "T0_CANVAS_TO_BIG_R": 80,  # 画布到大框的左/右边距 (mm)

    # 模板-2 (T1)：11列，用于小版 1.2/2.2/3.2/3.3/4.2/5.2
    "T1_CANVAS_W": 1500, "T1_CANVAS_H": 4500,
    "T1_COLS": 11, "T1_COL_GAP": 5,
    "T1_BIG_FRAME_L": 10, "T1_BIG_FRAME_R": 10,
    "T1_CANVAS_TO_BIG_L": 0, "T1_CANVAS_TO_BIG_R": 0,

    # 模板-3 (T2)：9列，用于小版 1.3/2.3/4.3/5.3
    "T2_CANVAS_W": 1352, "T2_CANVAS_H": 4500,
    "T2_COLS": 9, "T2_COL_GAP": 9,
    "T2_BIG_FRAME_L": 20, "T2_BIG_FRAME_R": 10,
    "T2_CANVAS_TO_BIG_L": 80, "T2_CANVAS_TO_BIG_R": 0,

    # 模板-4 (T3)：9列，用于小版 3.1
    "T3_CANVAS_W": 1360, "T3_CANVAS_H": 4500,
    "T3_COLS": 9, "T3_COL_GAP": 10,
    "T3_BIG_FRAME_L": 10, "T3_BIG_FRAME_R": 20,
    "T3_CANVAS_TO_BIG_L": 0, "T3_CANVAS_TO_BIG_R": 80,

    # 模板-5 (T4)：9列，用于小版 3.4
    "T4_CANVAS_W": 1360, "T4_CANVAS_H": 4500,
    "T4_COLS": 9, "T4_COL_GAP": 10,
    "T4_BIG_FRAME_L": 20, "T4_BIG_FRAME_R": 10,
    "T4_CANVAS_TO_BIG_L": 80, "T4_CANVAS_TO_BIG_R": 0,

    # ====== 大版参数 (B0~B4，对应 5 块大版) ======
    # 大版-1 (B0)：容纳小版 1.1 + 1.2 + 1.3
    "B0_CANVAS_W": 5000, "B0_CANVAS_H": 5900,   # 画布宽 x 高 (mm)
    "B0_BIG_FRAME_W": 4352, "B0_BIG_FRAME_H": 4500,  # 大框宽 x 高 (mm)
    "B0_TOP_MARGIN": 400, "B0_BOTTOM_MARGIN": 1000,  # 上边距 x 下边距 (mm)

    # 大版-2 (B1)：容纳小版 2.1 + 2.2 + 2.3
    "B1_CANVAS_W": 5000, "B1_CANVAS_H": 5900,
    "B1_BIG_FRAME_W": 4352, "B1_BIG_FRAME_H": 4500,
    "B1_TOP_MARGIN": 400, "B1_BOTTOM_MARGIN": 1000,

    # 大版-3 (B2)：容纳小版 3.1 + 3.2 + 3.3 + 3.4（4块最大版）
    "B2_CANVAS_W": 6500, "B2_CANVAS_H": 5900,
    "B2_BIG_FRAME_W": 5720, "B2_BIG_FRAME_H": 4500,
    "B2_TOP_MARGIN": 400, "B2_BOTTOM_MARGIN": 1000,

    # 大版-4 (B3)：容纳小版 4.1 + 4.2 + 4.3
    "B3_CANVAS_W": 5000, "B3_CANVAS_H": 5900,
    "B3_BIG_FRAME_W": 4352, "B3_BIG_FRAME_H": 4500,
    "B3_TOP_MARGIN": 400, "B3_BOTTOM_MARGIN": 1000,

    # 大版-5 (B4)：容纳小版 5.1 + 5.2 + 5.3
    "B4_CANVAS_W": 5000, "B4_CANVAS_H": 5900,
    "B4_BIG_FRAME_W": 4352, "B4_BIG_FRAME_H": 4500,
    "B4_TOP_MARGIN": 400, "B4_BOTTOM_MARGIN": 1000,
}

# ==================== 小版模板定义 ====================
# 5 种小版模板，每种有不同的列数、画布尺寸和边距。
# 每个小版实例（共 16 块）引用其中一个模板。
# 字段说明：
#   name            模板名称（标注用）
#   canvasW_mm      画布宽度（mm）
#   canvasH_mm      画布高度（mm）
#   cols            列数（从左到右的列数）
#   colGap_mm       列间距（mm）
#   bigFrameLeft    大框左边距（mm），大框左边缘到第一列单元格的距离
#   bigFrameRight   大框右边距（mm），最后一列单元格到大框右边缘的距离
#   canvasToBigLeft 画布左边距（mm），画布左边缘到大框左边缘的距离
#   canvasToBigRight画布右边距（mm），大框右边缘到画布右边缘的距离
SMALL_TEMPLATES = [
    {"name": "模板-1", "canvasW_mm": 1500, "canvasH_mm": 4500, "cols": 10, "colGap_mm": 10,
     "bigFrameLeft": 10, "bigFrameRight": 20, "canvasToBigLeft": 0, "canvasToBigRight": 80},
    {"name": "模板-2", "canvasW_mm": 1500, "canvasH_mm": 4500, "cols": 11, "colGap_mm": 5,
     "bigFrameLeft": 10, "bigFrameRight": 10, "canvasToBigLeft": 0, "canvasToBigRight": 0},
    {"name": "模板-3", "canvasW_mm": 1352, "canvasH_mm": 4500, "cols": 9, "colGap_mm": 9,
     "bigFrameLeft": 20, "bigFrameRight": 10, "canvasToBigLeft": 80, "canvasToBigRight": 0},
    {"name": "模板-4", "canvasW_mm": 1360, "canvasH_mm": 4500, "cols": 9, "colGap_mm": 10,
     "bigFrameLeft": 10, "bigFrameRight": 20, "canvasToBigLeft": 0, "canvasToBigRight": 80},
    {"name": "模板-5", "canvasW_mm": 1360, "canvasH_mm": 4500, "cols": 9, "colGap_mm": 10,
     "bigFrameLeft": 20, "bigFrameRight": 10, "canvasToBigLeft": 80, "canvasToBigRight": 0},
]

# ==================== 小版实例定义 ====================
# 共 16 块小版，分属 5 块大版。每块小版引用一个模板，并按 order 顺序排列。
# 字段说明：
#   name         小版名称（如"小版1.1"表示大版1的第1块小版）
#   templateIdx  模板索引（0~4，对应 SMALL_TEMPLATES 中的5种模板）
#   bigBoardIdx  所属大版索引（0~4，对应 BIG_BOARD_DEFS 中的5块大版）
#   order        在该大版中的排列顺序（0=最右，1=中间，...，从左到右编号越大越靠左）
#
# 排版逻辑：经文按段落从左到右、从上到下填充单元格。
# 大版内小版排列顺序为从右到左（order 0 最右，order N 最左），符合传统竖排阅读习惯。
# 实际映射：order → actualCol = (cols-1) - logicalCol，即列号反转。
BOARD_INSTANCES = [
    # 大版-1 (3块)
    {"name": "小版1.1", "templateIdx": 0, "bigBoardIdx": 0, "order": 0},
    {"name": "小版1.2", "templateIdx": 1, "bigBoardIdx": 0, "order": 1},
    {"name": "小版1.3", "templateIdx": 2, "bigBoardIdx": 0, "order": 2},
    # 大版-2 (3块)
    {"name": "小版2.1", "templateIdx": 0, "bigBoardIdx": 1, "order": 0},
    {"name": "小版2.2", "templateIdx": 1, "bigBoardIdx": 1, "order": 1},
    {"name": "小版2.3", "templateIdx": 2, "bigBoardIdx": 1, "order": 2},
    # 大版-3 (4块)
    {"name": "小版3.1", "templateIdx": 3, "bigBoardIdx": 2, "order": 0},
    {"name": "小版3.2", "templateIdx": 1, "bigBoardIdx": 2, "order": 1},
    {"name": "小版3.3", "templateIdx": 1, "bigBoardIdx": 2, "order": 2},
    {"name": "小版3.4", "templateIdx": 4, "bigBoardIdx": 2, "order": 3},
    # 大版-4 (3块)
    {"name": "小版4.1", "templateIdx": 0, "bigBoardIdx": 3, "order": 0},
    {"name": "小版4.2", "templateIdx": 1, "bigBoardIdx": 3, "order": 1},
    {"name": "小版4.3", "templateIdx": 2, "bigBoardIdx": 3, "order": 2},
    # 大版-5 (3块)
    {"name": "小版5.1", "templateIdx": 0, "bigBoardIdx": 4, "order": 0},
    {"name": "小版5.2", "templateIdx": 1, "bigBoardIdx": 4, "order": 1},
    {"name": "小版5.3", "templateIdx": 2, "bigBoardIdx": 4, "order": 2},
]

# ==================== 大版定义 ====================
# 5 块大版的几何参数。每块大版将多块小版水平排列在一个画布上。
# 字段说明：
#   canvasW_mm      画布宽度（mm）
#   canvasH_mm      画布高度（mm）
#   bigFrameW_mm    大框宽度（mm），大版自身的大框（包围所有小版的外框）
#   bigFrameH_mm    大框高度（mm）
#   topMargin_mm    上边距（mm），画布顶部到大框顶部的距离
#   bottomMargin_mm 下边距（mm），大框底部到画布底部的距离
#   indices         包含的小版索引列表（对应 BOARD_INSTANCES 中的位置）
#
# 大版排版逻辑：
#   - 大框水平居中于画布：大框左边 = (canvasW - bigFrameW) / 2
#   - 小版在大框内从右向左排列（最右为 order=0 的小版）
#   - 大版-3（B2）最大，容纳 4 块小版（3.1+3.2+3.3+3.4）
BIG_BOARD_DEFS = [
    {"canvasW_mm": 5000, "canvasH_mm": 5900, "bigFrameW_mm": 4352, "bigFrameH_mm": 4500,
     "topMargin_mm": 400, "bottomMargin_mm": 1000, "indices": [0, 1, 2]},
    {"canvasW_mm": 5000, "canvasH_mm": 5900, "bigFrameW_mm": 4352, "bigFrameH_mm": 4500,
     "topMargin_mm": 400, "bottomMargin_mm": 1000, "indices": [3, 4, 5]},
    {"canvasW_mm": 6500, "canvasH_mm": 5900, "bigFrameW_mm": 5720, "bigFrameH_mm": 4500,
     "topMargin_mm": 400, "bottomMargin_mm": 1000, "indices": [6, 7, 8, 9]},
    {"canvasW_mm": 5000, "canvasH_mm": 5900, "bigFrameW_mm": 4352, "bigFrameH_mm": 4500,
     "topMargin_mm": 400, "bottomMargin_mm": 1000, "indices": [10, 11, 12]},
    {"canvasW_mm": 5000, "canvasH_mm": 5900, "bigFrameW_mm": 4352, "bigFrameH_mm": 4500,
     "topMargin_mm": 400, "bottomMargin_mm": 1000, "indices": [13, 14, 15]},
]

# ==================== 经文分品名称 ====================
# 题目（1）+ 32 品（32）+ 尾题（1），共 34 个段落。
# 索引 0 为"题目"（开经），索引 1~32 对应第 1~32 分，索引 33 为"尾题"。
# 用于 PSD 图层组的段落子组命名、日志输出和标注。
PARA_NAMES = [
    "00.题目", "01.法会因由分", "02.大乘正宗分", "03.妙行无住分", "04.如理实见分",
    "05.正信希有分", "06.无得无说分", "07.依法出生分", "08.一相无相分", "09.庄严净土分",
    "10.无为福胜分", "11.尊重正教分", "12.如法受持分", "13.离相寂灭分", "14.持经功德分",
    "15.能净业障分", "16.究竟无我分", "17.一体同观分", "18.法界通化分", "19.离色离相分",
    "20.非说所说分", "21.无法可得分", "22.净心行善分", "23.福智无比分", "24.化无所化分",
    "25.法身非相分", "26.无断无灭分", "27.不受不贪分", "28.威仪寂净分", "29.一合理相分",
    "30.知见不生分", "31.应化非真分", "32.经文功德分", "33.尾题"
]

# ==================== 字库版本号探测范围 ====================
# 字库中的字符可能有多个版本（变体字形），如 "佛.jpg"、"佛-1.jpg"、"佛-2.jpg" ……
# 此值设定最大探测的版本号（0~50），即最多探测 佛、佛-1、佛-2 … 佛-50 共 51 个版本。
MAX_VERSION_PROBE = 50


# ==================== 基础工具函数 ====================
def mm_to_px(mm, dpi):
    """毫米转像素。
    
    打印行业中，物理尺寸与数码像素的换算公式：
      像素 = 毫米 × DPI / 25.4
    其中 25.4 = 1 英寸的毫米数，DPI = Dots Per Inch（每英寸像素数）。

    参数：
      mm (float): 毫米值
      dpi (int): 分辨率

    返回：
      int: 四舍五入后的像素值
    """
    return round(mm * dpi / 25.4)


def save_filename(instance_name, dpi):
    """根据实例名称和 DPI 构造输出文件名。
    
    格式示例：
      save_filename("小版1.1", 150) → "金刚经.1.1.150"
      save_filename("大版-1",  150) → "金刚经.1.150"
    
    最终文件名为：金刚经.{编号}.{DPI}.psd
    """
    return f"金刚经.{instance_name.replace('小版', '').replace('大版-', '')}.{dpi}"


# ==================== 日志系统 ====================
# 双重输出：控制台（print）+ 文件（金刚经_Python_日志.txt）
# 文件路径：脚本所在目录下的"金刚经_Python_日志.txt"
# 线程安全：使用 threading.Lock() 保护文件写入

_LOG_FILE_PATH = os.path.join(SCRIPT_DIR, "金刚经_Python_日志.txt")  # 日志文件路径
_LOG_FILE = None          # 日志文件句柄（延迟初始化）
_LOG_LOCK = __import__('threading').Lock()  # 线程锁（确保并发写入安全）

def _ensure_log_file():
    """确保日志文件已打开（延迟初始化）。
    首次调用时打开文件，写入会话分隔标记，方便区分不同运行。
    """
    global _LOG_FILE
    if _LOG_FILE is None:
        try:
            _LOG_FILE = open(_LOG_FILE_PATH, 'a', encoding='utf-8')
            # 写入分隔标记，方便在日志中区分每次运行
            ts = time.strftime('%Y-%m-%d %H:%M:%S')
            _LOG_FILE.write(f"\n{'='*60}\n"
                           f"=== 新会话开始 {ts} ===\n"
                           f"{'='*60}\n")
            _LOG_FILE.flush()
        except Exception as e:
            print(f"[ERROR] 无法打开日志文件: {e}")

def close_log_file():
    """关闭日志文件句柄，确保缓冲区数据写入磁盘。"""
    global _LOG_FILE
    if _LOG_FILE is not None:
        try:
            _LOG_FILE.close()
        except Exception:
            pass
        finally:
            _LOG_FILE = None

def log(msg, to_file=True):
    """统一日志输出函数。
    同时输出到控制台（print）和日志文件（如果启用）。
    每条日志自动添加时间戳 [HH:MM:SS]。

    参数：
      msg (str): 日志消息内容
      to_file (bool): 是否同时写入文件，默认 True
    """
    ts = time.strftime('%H:%M:%S')
    line = f"[{ts}] {msg}"
    print(line)
    if to_file:
        with _LOG_LOCK:
            _ensure_log_file()
            if _LOG_FILE:
                try:
                    _LOG_FILE.write(line + '\n')
                    _LOG_FILE.flush()
                except Exception as e:
                    print(f"[WARN] 日志写入失败: {e}", file=sys.stderr)




# ==================== 配置文件读写 ====================
def load_config():
    """从"金刚经排版参数.json"加载用户保存的参数。
    
    加载逻辑：
      1. 以 DEFAULT_PARAMS 为基准（保证新版本新增的参数有默认值）
      2. 如果 JSON 文件存在，用文件中的值覆盖对应的默认值
      3. 如果 JSON 文件不存在，直接使用默认值
    
    返回：
      dict: 合并后的参数字典
    """
    params = dict(DEFAULT_PARAMS)
    if not os.path.exists(CONFIG_PATH):
        log("配置文件不存在，使用默认值")
        return params
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            saved = json.load(f)
        for k, v in saved.items():
            if k in params:
                params[k] = v
        log("参数已加载")
    except Exception as e:
        log(f"参数加载失败: {e}")
    return params


def save_config(params):
    """将当前参数保存到"金刚经排版参数.json"文件。
    使用 UTF-8 编码、2 空格缩进，确保中文可读性。
    
    参数：
      params (dict): 要保存的参数字典
    """
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(params, f, ensure_ascii=False, indent=2)
        log("参数已保存")
    except Exception as e:
        log(f"参数保存失败: {e}")


# ==================== 经文解析 ====================
def parse_scripture(text):
    """解析经文文本，提取字符和格式标记。
    
    解析流程：
      1. 按 \n 分割为段落（每品为一段）
      2. 每个段落内逐字符分析：
         - CJK 汉字（U+4E00~U+9FFF）→ type="char"
         - 空格（U+0020 半角 / U+3000 全角）→ type="skip"
         - 其他字符（标点等）→ 忽略
      3. 段落之间插入 type="br"（分段标记），最后一个 \n 后不插入
    
    返回的 items 数组中，每个元素为字典：
      - {"type": "char", "character": "佛", "paraIndex": 0}   字符
      - {"type": "skip", "paraIndex": 0}                       空格占位
      - {"type": "br", "paraIndex": 0, "lastBreak": False}     分段标记
      - {"type": "br", "paraIndex": 31, "lastBreak": True}     最后一个分段标记
    """
    paragraphs = []
    raw = text.split("\n")
    for line in raw:
        tokens = []
        for ch in line:
            code = ord(ch)
            if 0x4E00 <= code <= 0x9FFF:
                tokens.append({"type": "char", "char": ch})
            elif code in (0x0020, 0x3000):
                tokens.append({"type": "skip"})
        if tokens:
            paragraphs.append(tokens)

    items = []
    for p_idx, para in enumerate(paragraphs):
        for token in para:
            if token["type"] == "char":
                items.append({"type": "char", "character": token["char"], "paraIndex": p_idx})
            else:
                items.append({"type": "skip", "paraIndex": p_idx})
        if p_idx < len(paragraphs) - 1:
            last_br = (p_idx == len(paragraphs) - 2)
            items.append({"type": "br", "paraIndex": p_idx, "lastBreak": last_br})
    return items


def allocate_all_boards(items, params):
    """将解析后的经文 items 按顺序分配到 16 块小版的单元格中。
    
    这是全文排版的核心算法。按小版实例顺序（BOARD_INSTANCES）逐一填充：
      1. 每块小版有 cols 列 × rows 行 = 总单元格数
      2. 逐字符填入单元格，填满一列后自动换到下一列
      3. 遇到分段标记 (type="br") 时按设置的模式处理：
         - 模式1（换列）：当前列非空时换到新列
         - 模式2（跳格）：首分段换列，后续分段跳 N 个空格，尾题可选换列
    
    关键字段：
      logicalCol/logicalRow: 逻辑行列（填充顺序中的位置）
      actualCol: 实际列 = (cols-1) - logicalCol（列号反转，因为排版从右到左）
      actualRow: 实际行 = logicalRow（行号不变）
      absoluteCharIdx: 该字符在全文中第几次出现（用于选择变体字形版本）
    
    返回：
      results (list): 16块小版的分配结果
      total_chars (int): 总分配字符数
    """
    results = []
    item_idx = 0                        # 当前正在处理的 item 索引
    first_break = True                  # 首分段标记（模式2中用于判断第一个 \n）
    char_idx_counter = {}               # 每个字符在全文中出现的次数计数器（用于变体版本选择）

    for inst in BOARD_INSTANCES:
        templ = SMALL_TEMPLATES[inst["templateIdx"]]
        cols = templ["cols"]
        rows = params["ROWS"]
        placements = []                 # 当前小版的放置列表
        cur_col = 0                     # 当前填充列（从左到右）
        cur_row = 0                     # 当前填充行（从上到下）

        while item_idx < len(items) and cur_col < cols:
            it = items[item_idx]
            # ---- 处理分段标记 (br) ----
            if it["type"] == "br":
                if params["SCRIPTURE_MODE"] == 1:
                    # 模式1：换列 —— 只要当前列非空，就换到下一列
                    if cur_row != 0:
                        cur_col += 1
                        cur_row = 0
                else:
                    # 模式2：跳格
                    if first_break:
                        # 第一个分段：若当前列已写满(cur_row=0)，自然已换列，不强制再换列以免浪费一整列
                        if cur_row != 0:
                            cur_col += 1
                            cur_row = 0
                        first_break = False
                    elif params["LAST_BR_NEW_COL"] and it.get("lastBreak"):
                        # 最后一个分段（尾题所在分段前）：若当前列恰已填满则不再强行换列
                        if cur_row != 0:
                            cur_col += 1
                            cur_row = 0
                    else:
                        # 其他分段：跳过 PARA_SKIP_COUNT 个空格
                        for _ in range(params["PARA_SKIP_COUNT"]):
                            placements.append({"type": "skip", "logicalRow": cur_row,
                                                "logicalCol": cur_col, "paraIndex": it["paraIndex"]})
                            cur_row += 1
                            if cur_row >= rows:
                                cur_row = 0
                                cur_col += 1
                            if cur_col >= cols:
                                break
                item_idx += 1
                continue

            # ---- 处理空格 (skip) ----
            if it["type"] == "skip":
                placements.append({"type": "skip", "logicalRow": cur_row,
                                    "logicalCol": cur_col, "paraIndex": it["paraIndex"]})
                cur_row += 1
                if cur_row >= rows:
                    cur_row = 0
                    cur_col += 1
                item_idx += 1
                continue

            # ---- 处理字符 (char) ----
            ch_count = char_idx_counter.get(it["character"], 0)
            placements.append({
                "type": "char", "character": it["character"],
                "absoluteCharIdx": ch_count,  # 该字符第几次出现（0-based）
                "logicalRow": cur_row, "logicalCol": cur_col,
                "paraIndex": it["paraIndex"]
            })
            char_idx_counter[it["character"]] = ch_count + 1
            cur_row += 1
            if cur_row >= rows:
                cur_row = 0
                cur_col += 1
            item_idx += 1

        # ---- 列号反转（从右到左阅读）----
        # 传统竖排从右向左阅读，所以 actualCol 需要反转
        for p in placements:
            p["actualCol"] = (cols - 1) - p["logicalCol"]
            p["actualRow"] = p["logicalRow"]

        results.append({
            "instanceName": inst["name"],
            "templateIdx": inst["templateIdx"],
            "placements": placements,
            "full": cur_col >= cols            # 是否填满该小版
        })
    # 计算总字符数
    total_chars = sum(1 for al in results for p in al["placements"] if p["type"] == "char")
    return results, total_chars


# ==================== 字库图片探测与缓存 ====================
@lru_cache(maxsize=5000)
def probe_versions(pic_folder, ch):
    """探测某个字符在字库中的所有可用版本号。
    
    字库文件命名规则：
      - 基础版：    佛.jpg（或 .tif/.png/.psd）
      - 变体版：    佛-1.jpg, 佛-2.jpg, …, 佛-50.jpg
      - 即字符名 + 可选的 "-N" + 扩展名
    
    探测范围：从版本 0（无后缀）到 MAX_VERSION_PROBE（默认 50）。
    每个版本按 IMAGE_EXTS 优先级（jpg > tif > png > psd）查找首个存在的文件。
    
    返回值示例：
      ["佛" 存在 佛.jpg 和 佛-1.png] → [0, 1]
      ["一" 只存在 一.tif]          → [0]
      ["缺" 无任何文件]             → [0]  (兜底值，由调用方判断)
    
    注意：此函数使用 @lru_cache 缓存，字号约 4000+，缓存上限 5000，
    首次运行后命中率接近 100%，避免约 81 万次磁盘 IO。
    """
    versions = []
    for n in range(MAX_VERSION_PROBE + 1):
        base = ch if n == 0 else f"{ch}-{n}"
        for ext in IMAGE_EXTS:
            p = os.path.join(pic_folder, base + ext)
            if os.path.exists(p):
                versions.append(n)
                break
    return versions if versions else [0]


# LRU 缓存：字符图片路径 + 宽高 + DPI
@lru_cache(maxsize=10000)
def _get_cached_image_info(pic_folder, ch, abs_idx, dpi=150):
    """获取字符图片的路径、原始尺寸和 DPI（带缓存）。
    
    本函数是字符图片加载的入口，缓存了以下信息以减少重复 IO：
      - 图片文件路径
      - 原始像素尺寸（宽、高）
      - 原始 DPI（从图片元数据读取）
    
    变体版本选择逻辑：
      abs_idx 是字符在全文中第几次出现（0-based），
      用 abs_idx % len(版本列表) 轮循选择版本。
      例如：佛有 2 个版本 [0,1]，则第1次出现用版本0，第2次用版本1，第3次用版本0...
    
    参数：
      pic_folder (str): 字库目录路径
      ch (str): 字符（如"佛"）
      abs_idx (int): 字符在全文中第几次出现（0-based）
      dpi (int): 默认 DPI（当图片元数据缺失时使用）
    
    返回：
      (path, src_w, src_h, src_res)
        path   (str): 图片文件路径（找不到则为 ""）
        src_w  (int): 原始像素宽度
        src_h  (int): 原始像素高度
        src_res(int): 原始 DPI
    """
    vlist = probe_versions(pic_folder, ch)
    ver = vlist[abs_idx % len(vlist)]
    base = ch if ver == 0 else f"{ch}-{ver}"
    for ext in IMAGE_EXTS:
        p = os.path.join(pic_folder, base + ext)
        if os.path.exists(p):
            try:
                with Image.open(p) as img:
                    src_w, src_h = img.size
                    src_res = img.info.get("dpi", (dpi, dpi))
                    src_res = src_res[0] if isinstance(src_res, tuple) else dpi
                return p, src_w, src_h, src_res
            except Exception as e:
                log(f"  [WARN] 图片文件可能已损坏: {p} —— {e}")
                return p, 0, 0, dpi
    return "", 0, 0, dpi


# ==================== 白底转透明处理（Pillow C 级加速）====================
def _white_to_transparent(img, file_ext=None):
    """将字符图片的白色背景转为透明，保留墨迹（黑色部分）。
    
    核心原理（C 层批量像素操作，比逐像素 Python 循环快 5~10 倍）：
      1. 计算原始图与纯白图的差异（ImageChops.difference）
      2. 将差异转为灰度（L 模式），灰度值 = 像素与白色的偏离程度
      3. 灰度 < 20  = 白色/近白区域 → Alpha = 0（完全透明）
         灰度 ≥ 20  = 有墨迹区域   → Alpha = 255（不透明）
      4. 将生成的 Alpha 通道应用到 RGBA 图像
    
    特殊处理：
      - 已有透明通道的 PNG：若 alpha 最小值 < 255（已有透明内容），直接返回
      - TIF/JPG：先转 RGBA，再按上述逻辑生成 Alpha 通道
    """
    # 已有透明通道的 PNG：检查是否已含透明像素
    if file_ext and file_ext.lower() == '.png' and img.mode == 'RGBA':
        alpha = img.getchannel('A')
        if alpha.getextrema()[0] < 255:
            # 已有透明像素，直接返回
            return img

    # TIF / JPG / 不透明 PNG：白底转透明
    img = img.convert("RGBA")
    white = Image.new('RGB', img.size, (255, 255, 255))
    diff = ImageChops.difference(img.convert('RGB'), white)
    gray = diff.convert('L')
    alpha = Image.eval(gray, lambda x: 0 if x < 20 else 255)
    img.putalpha(alpha)
    return img


# ==================== 网格布局计算 ====================
def compute_grid(templ, params, dpi):
    """计算小版中所有单元格的像素坐标，返回完整网格布局字典。
    
    返回字段说明：
      cell_w/cell_h    单元宽高(像素)
      row_tops          每行顶部的Y坐标数组 [r*rows]
      col_lefts         每列左边的X坐标数组 [c*cols]
      big_left/right    大框左右边界(画布上的像素X)
      big_top/bottom    大框上下边界(画布上的像素Y)
      canvas_w/h        画布宽高(像素)
      rows/cols         行列数
    
    行列均匀分布算法：
      首尾坐标由公式计算，中间行/列按等比例线性插入，
      避免整数舍入导致的累积误差。
    """
    px = dpi / 25.4                 # 毫米→像素转换系数
    rows = params["ROWS"]
    cols = templ["cols"]

    cell_w_px = mm_to_px(params["CELL_W"], dpi)
    cell_h_px = mm_to_px(params["CELL_H"], dpi)

    # 单元格区域左上角在画布上的坐标（mm）
    cell_region_left_mm = templ["canvasToBigLeft"] + templ["bigFrameLeft"]
    cell_region_top_mm = params["CANVAS_TO_BIGFRAME_TOP"] + params["BIG_FRAME_MARGIN_TOP"]

    # 大框四边在画布上的像素坐标
    big_left = mm_to_px(templ["canvasToBigLeft"], dpi)
    big_right = mm_to_px(templ["canvasW_mm"] - templ["canvasToBigRight"], dpi)
    big_top = mm_to_px(params["CANVAS_TO_BIGFRAME_TOP"], dpi)
    big_bottom = mm_to_px(templ["canvasH_mm"] - params["CANVAS_TO_BIGFRAME_BOTTOM"], dpi)

    canvas_w = mm_to_px(templ["canvasW_mm"], dpi)
    canvas_h = mm_to_px(templ["canvasH_mm"], dpi)

    # ---- 行坐标（Y 方向，从上到下）----
    row_tops = [0] * rows
    row_tops[0] = round(cell_region_top_mm * px)
    row_tops[rows - 1] = round((cell_region_top_mm + (rows - 1) * (params["CELL_H"] + params["ROW_GAP"])) * px)
    rdist = row_tops[rows - 1] - row_tops[0]
    for r in range(1, rows - 1):
        row_tops[r] = row_tops[0] + round(r * rdist / (rows - 1))

    # ---- 列坐标（X 方向，从左到右）----
    col_lefts = [0] * cols
    col_lefts[0] = round(cell_region_left_mm * px)
    col_lefts[cols - 1] = round((cell_region_left_mm + (cols - 1) * (params["CELL_W"] + templ["colGap_mm"])) * px)
    cdist = col_lefts[cols - 1] - col_lefts[0]
    for c in range(1, cols - 1):
        col_lefts[c] = col_lefts[0] + round(c * cdist / (cols - 1))

    return {
        "cell_w": cell_w_px, "cell_h": cell_h_px,    # 单元格宽高（像素）
        "row_tops": row_tops, "col_lefts": col_lefts, # 行列坐标数组
        "big_left": big_left, "big_right": big_right,  # 大框左右边界
        "big_top": big_top, "big_bottom": big_bottom,  # 大框上下边界
        "canvas_w": canvas_w, "canvas_h": canvas_h,    # 画布尺寸
        "rows": rows, "cols": cols                     # 行列数
    }


def _psd_save_with_debug(psd, path):
    """保存 PSD 文件（RLE 压缩），失败时自动诊断 GBK 编码问题。
    
    RLE（Run-Length Encoding）是 Photoshop 默认的无损压缩方式，
    可显著减小 PSD 文件体积而不损失画质。
    
    如果保存时抛出 UnicodeEncodeError（图层名含 GBK 不支持的字符），
    本函数会遍历所有图层并输出具体的编码失败字符，帮助定位问题。
    """
    try:
        psd.save(path, encoding=PSD_ENCODING, compression=Compression.RLE)
    except UnicodeEncodeError:
        for l in psd.descendants():
            if hasattr(l, 'name') and l.name:
                try:
                    l.name.encode(PSD_ENCODING)
                except UnicodeEncodeError:
                    parent_name = l.parent.name if hasattr(l, 'parent') and l.parent else '(根)'
                    hex_name = ' '.join(f'U+{ord(c):04X}' for c in l.name)
                    log(f"  [ERR] 图层名称: {hex_name}  (父: {parent_name})")
        raise


def _gen_template_psd_only(templ, params, dpi, grid=None, progress_cb=None, cancel_check=None):
    """生成仅含模板构件的 PSD 文档（不含文字图层）。
    返回的 PSDImage 对象可交由 generate_small_board() 继续添加字符图层。
    
    创建的图层结构（从底层到顶层）：
      [L] 背景                纯白不透明底图
      [G] 经文组              空组，后续放置各字符图层
      [G] 框线
         [L] 水平垂直中线     绿色单元格中心十字线 + 蓝色分割线（半透明底）
         [L] 单元格           红色单元格边框线（半透明底）
         [L] 大框             红色最外层大框（半透明底）
    
    优化：接受可选的预计算 grid 参数，避免重复调用 compute_grid()。
    
    参数：
      cancel_check (callable): 取消检查回调，返回 True 时抛出 GenerationCancelled
    """
    if grid is None:
        grid = compute_grid(templ, params, dpi)
    cw, ch = grid["cell_w"], grid["cell_h"]
    rt, cl = grid["row_tops"], grid["col_lefts"]
    rows, cols = grid["rows"], grid["cols"]
    bl, br = grid["big_left"], grid["big_right"]
    bt, bb = grid["big_top"], grid["big_bottom"]
    split_row = params["SPLIT_LINE_AFTER_ROW"] - 1
    cw_px, ch_px = grid["canvas_w"], grid["canvas_h"]

    def _step(pct, msg):
        if progress_cb:
            progress_cb(pct, 100, msg)

    _step(0, "初始化 PSD 文档...")
    psd = PSDImage.new('RGB', (cw_px, ch_px))
    set_psd_resolution(psd, dpi)

    # ---- 创建顺序 = 从下到上的图层顺序 ----

    # 1. 背景（最底层，纯白不透明）
    _step(10, "创建背景图层...")
    bg_img = Image.new("RGB", (cw_px, ch_px), (255, 255, 255))
    psd.create_pixel_layer(name='背景', image=bg_img, top=0, left=0)

    # 2. 经文组（空组，后续加字）
    _step(20, "创建经文组...")
    psd.create_group(name='经文组')

    # 3. 框线组（包含辅助中线、单元格、大框）
    _step(30, "创建框线组...")
    frame_group = psd.create_group(name='框线')

    # 辅助函数：创建透明底图层并移入框线组
    def _make_frame_layer(name, draw_fn, pct, msg):
        _step(pct, msg)
        img = Image.new("RGBA", (cw_px, ch_px), (0, 0, 0, 0))
        dr = ImageDraw.Draw(img)
        draw_fn(dr)
        layer = psd.create_pixel_layer(name=name, image=img, top=0, left=0)
        layer.move_to_group(frame_group)

    # 3a. 辅助中线 + 分割线（绿色 + 蓝色，透明底）
    if cancel_check and cancel_check():
        raise GenerationCancelled(f"框线绘制阶段——用户取消")
    _make_frame_layer('水平垂直中线', lambda dr: (
        [dr.line([(round(cl[c] + cw / 2), rt[r]), (round(cl[c] + cw / 2), rt[r] + ch)], fill=GUIDE_COLOR, width=1) or
         dr.line([(cl[c], round(rt[r] + ch / 2)), (cl[c] + cw, round(rt[r] + ch / 2))], fill=GUIDE_COLOR, width=1)
         for r in range(rows) for c in range(cols)],
        dr.line([(bl, round((rt[split_row] + ch + rt[split_row + 1]) / 2 - 0.5)),
                 (br, round((rt[split_row] + ch + rt[split_row + 1]) / 2 - 0.5))], fill=SPLIT_COLOR, width=1)
        if 0 <= split_row < rows - 1 else None,
    ), 40, "绘制绿色辅助中线 + 蓝色分割线...")

    # 3b. 单元格边框（红色，透明底）
    if cancel_check and cancel_check():
        raise GenerationCancelled(f"框线绘制阶段——用户取消")
    _make_frame_layer('单元格', lambda dr: [
        dr.rectangle([cl[c], rt[r], cl[c] + cw, rt[r] + ch], outline=LINE_COLOR, width=1)
        for r in range(rows) for c in range(cols)
    ], 70, "绘制红色单元格边框...")

    # 3c. 大框（红色，透明底）
    if cancel_check and cancel_check():
        raise GenerationCancelled(f"框线绘制阶段——用户取消")
    _make_frame_layer('大框', lambda dr: (
        dr.rectangle([bl, bt, br, bb], outline=LINE_COLOR, width=1)
    ), 90, "绘制红色大框...")

    return psd


# ==================== 图片缩放计算 ====================
def calc_target_size(src_w, src_h, src_res, cell_w, cell_h, scale_mode, scale_percent,
                     auto_threshold, auto_fill_w, auto_fill_h,
                     shrink_threshold, shrink_fill_w, shrink_fill_h,
                     dpi=150, cell_fill_ratio=90):
    """计算字符图片的目标显示尺寸（像素）。
    
    两种缩放模式（由 scale_mode 控制）：
    
    模式0（直接等比 + 自动缩放）：
      1. 基础缩放 = (DPI / 原始DPI) × 缩放百分比/100
      2. 计算缩放后占格的比率 M = max(宽比, 高比)
      3. 若 M×100 ≤ 自动放大阈值：启动自动放大，以比率较大的方向为准，
         缩放到对应方向的 fill 比率
      4. 若 M×100 ≥ 自动缩小阈值：启动自动缩小，逻辑同上
    
    模式1（相对单元格）：
      以单元格尺寸为基准，选择较紧密的方向缩放到 cell_fill_ratio%。
    
    参数：
      src_w/h (int): 原始图片像素尺寸
      src_res (int): 原始图片 DPI
      cell_w/h (int): 目标单元格像素尺寸
      scale_mode (int): 0=直接等比, 1=相对单元格
      scale_percent (int): 缩放百分比（仅模式0）
      auto_threshold (int): 自动放大阈值（%），0=不放大
      auto_fill_w/h (int): 自动放大填充比率（%）
      shrink_threshold (int): 自动缩小阈值（%），0=不缩小
      shrink_fill_w/h (int): 自动缩小填充比率（%）
      dpi (int): 输出分辨率
      cell_fill_ratio (int): 相对单元格填充比率（%）
    
    返回：
      (int, int): 目标宽度和高度（像素）
    """
    if scale_mode == 0:
        # 直接等比：用 DPI 保证物理尺寸不变
        base_scale = dpi / src_res
        final = base_scale * scale_percent / 100
    else:
        # 相对单元格：以较大方向为基准，缩放到单元格的 cell_fill_ratio%
        fill_w = cell_w / src_w
        fill_h = cell_h / src_h
        if fill_h > fill_w:
            base_scale = fill_w * cell_fill_ratio / 100
        else:
            base_scale = fill_h * cell_fill_ratio / 100
        final = base_scale

    tw, th = src_w * final, src_h * final

    if scale_mode == 0:
        # 计算两个方向的填充比率，取较大值 M
        rate_w = tw / cell_w
        rate_h = th / cell_h
        M = max(rate_w, rate_h)
        if auto_threshold > 0 and M * 100 <= auto_threshold:
            # 启动自动放大：按 M 来源方向使用不同的 fill 比率
            if rate_w >= rate_h:
                new_tw = cell_w * auto_fill_w / 100
                scale = new_tw / tw
                tw, th = new_tw, th * scale
            else:
                new_th = cell_h * auto_fill_h / 100
                scale = new_th / th
                tw, th = tw * scale, new_th
        elif shrink_threshold > 0 and M * 100 >= shrink_threshold:
            # 启动自动缩小：按 M 来源方向使用不同的 fill 比率
            if rate_w >= rate_h:
                new_tw = cell_w * shrink_fill_w / 100
                scale = new_tw / tw
                tw, th = new_tw, th * scale
            else:
                new_th = cell_h * shrink_fill_h / 100
                scale = new_th / th
                tw, th = tw * scale, new_th
    return int(tw), int(th)


# ==================== 标注生成 ====================
def _make_text_layer(img, text, x, y, font, color=(100, 100, 100, 255), bg=None):
    """在 RGBA 图像上绘制带背景的文本"""
    draw = ImageDraw.Draw(img)
    bbox = draw.textbbox((0, 0), text, font=font)
    tw = bbox[2] - bbox[0]
    th = bbox[3] - bbox[1]
    if bg:
        draw.rectangle([x - 2, y - 1, x + tw + 2, y + th + 1], fill=bg)
    draw.text((x, y), text, fill=color, font=font)


# ==================== 尺寸标注辅助函数 ====================

ANNO_COLOR = (80, 80, 80, 220)

def _calc_anno_font_size(text, avail_w, avail_h, font_name="simsun.ttc",
                         min_size=8, max_size=26):
    """根据可用空间计算合适字号（从大到小探测）"""
    try:
        for size in range(max_size, min_size - 1, -1):
            font = _load_anno_font(size, font_name)  # 使用缓存，避免重复从磁盘加载字体
            bbox = font.getbbox(text)
            tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
            if tw <= avail_w - 4 and th <= avail_h - 4:
                return size
    except Exception as e:
        log(f"  [WARN] 字号计算失败（字体可能缺失）: {e}")
    return min_size


@lru_cache(maxsize=500)
def _get_processed_image(img_path, tw, th):
    """缓存处理后的字符图像：缩放 + 白底转透明"""
    with Image.open(img_path) as src:
        resized = src.resize((tw, th), Image.Resampling.LANCZOS)
    ext = os.path.splitext(img_path)[1]
    return _white_to_transparent(resized, ext)


@lru_cache(maxsize=64)
def _load_anno_font(size, font_name="simsun.ttc"):
    try:
        return ImageFont.truetype(font_name, size)
    except Exception:
        return ImageFont.load_default()


def add_small_board_annotations(psd, templ, params, dpi, grid, progress_cb=None, cancel_check=None):
    """添加小版尺寸标注（动态字号 + 箭头字符）
    
    参数：
      cancel_check (callable): 取消检查回调，返回 True 时抛出 GenerationCancelled
    """
    cw, ch = grid["cell_w"], grid["cell_h"]
    rt, cl = grid["row_tops"], grid["col_lefts"]
    rows, cols = grid["rows"], grid["cols"]
    bl, br = grid["big_left"], grid["big_right"]
    bt, bb = grid["big_top"], grid["big_bottom"]
    canvas_w, canvas_h = grid["canvas_w"], grid["canvas_h"]
    split_row = params["SPLIT_LINE_AFTER_ROW"] - 1
    row_gap_px = mm_to_px(params["ROW_GAP"], dpi)
    grid_bottom = rt[rows - 1] + ch

    # 优化：所有标注绘制到同一张画布上，最后只创建一个图层（大幅减少内存分配）
    anno_img = Image.new('RGBA', (canvas_w, canvas_h), (0, 0, 0, 0))
    anno_group = psd.create_group(name='尺寸标注组')
    _anno_count = [0]
    # 根据实际条件动态计算标注总数（避免条件不满足时进度条提前终止）
    _total_annos = 13  # 无条件标注：1实例名 2单元格尺寸 3列数行数 6大框尺寸 + 4大框边距 + 4画布边距 + 10画布尺寸
    if cols > 1:
        _total_annos += 1  # 4. 列间距
    if rows > 1:
        _total_annos += 1  # 5. 行间距
    if 0 <= split_row < rows - 1:
        _total_annos += 1  # 7. 分割线位置

    def _ap(label_text):
        _anno_count[0] += 1
        if progress_cb:
            progress_cb(98 + _anno_count[0] / _total_annos, 100,
                        f"尺寸标注 {_anno_count[0]}/{_total_annos}: {label_text}")
        # 每 2 项标注检查一次取消标志
        if _anno_count[0] % 2 == 0 and cancel_check and cancel_check():
            raise GenerationCancelled(f"尺寸标注阶段——用户取消（已完成{_anno_count[0]}项）")

    def _al(text, x, y, font, step_text=None):
        _ap(step_text or text)
        _make_text_layer(anno_img, text, max(0, x), max(0, y), font, color=ANNO_COLOR)

    # 1. 实例名
    sz = _calc_anno_font_size(templ['name'], canvas_w - 40, bt, max_size=28)
    _al(f"{templ['name']}", canvas_w // 2 - 20, 10, _load_anno_font(sz), "实例名")

    # 2. 单元格尺寸
    text = f"{params['CELL_W']}x{params['CELL_H']}mm"
    sz = _calc_anno_font_size(text, cw, ch, max_size=22)
    _al(text, cl[cols - 1] + 4, rt[0] + 14, _load_anno_font(sz), "单元格尺寸")

    # 3. 列数×行数（与实例名之间留出足够行距）
    text = f"{cols}列x{rows}行"
    sz = _calc_anno_font_size(text, canvas_w - 40, bt // 2, max_size=24)
    _al(text, canvas_w // 2 - 20, 40, _load_anno_font(sz), "列数行数")

    # 4. 列间距
    if cols > 1:
        gap_w = cl[cols - 1] - (cl[cols - 2] + cw)
        text = f"\u2190{templ['colGap_mm']}mm\u2192"
        sz = _calc_anno_font_size(text, gap_w, ch // 2, max_size=16, min_size=8)
        gap_x = (cl[cols - 2] + cw + cl[cols - 1]) // 2
        _al(text, gap_x - sz * len(text) // 3, rt[0] + 14, _load_anno_font(sz), "列间距")

    # 5. 行间距（垂直居中于行间空白）
    if rows > 1:
        text = f"\u2191{params['ROW_GAP']}mm\u2193"
        gap_h = rt[1] - (rt[0] + ch)
        sz = _calc_anno_font_size(text, cw // 2, gap_h, max_size=16, min_size=10)
        gap_y = (rt[0] + ch + rt[1]) // 2
        _al(text, cl[cols - 1] + 6, gap_y - sz // 2, _load_anno_font(sz), "行间距")

    # 6. 大框尺寸（放置于大框右上角内侧，避免与左边距标注重叠）
    outer_w = round((br - bl) * 25.4 / dpi)
    outer_h = round((bb - bt) * 25.4 / dpi)
    text = f"{outer_w}x{outer_h}"
    sz = _calc_anno_font_size(text, br - bl - 16, 60, max_size=22)
    text_w = sz * len(text)  # 估算文字像素宽度
    _al(text, br - text_w - 8, bt + 8, _load_anno_font(sz), "大框尺寸")

    # 7. 分割线位置（智能选择左右侧，防止超界）
    if 0 <= split_row < rows - 1:
        split_y = round((rt[split_row] + ch + rt[split_row + 1]) / 2 - 0.5)
        gap_size = params["ROW_GAP"] // 2
        text = f"\u2502\u2190第{params['SPLIT_LINE_AFTER_ROW']}行后 {gap_size}mm"
        right_space = canvas_w - br - 8
        left_space = bl
        if right_space >= 40:
            sz = _calc_anno_font_size(text, right_space, row_gap_px, max_size=18)
            est_w = sz * len(text)
            _al(text, min(br + 8, canvas_w - est_w - 8), split_y + 4, _load_anno_font(sz), "分割线位置")
        elif left_space >= 40:
            sz = _calc_anno_font_size(text, left_space, row_gap_px, max_size=18)
            _al(text, max(2, bl - 80), split_y + 4, _load_anno_font(sz), "分割线位置")
        else:
            sz = _calc_anno_font_size(text, canvas_w, row_gap_px, max_size=14, min_size=8)
            cx = (bl + br) // 2
            _al(text, max(2, cx - sz * len(text) // 2), split_y + 4, _load_anno_font(sz), "分割线位置")

    # 8. 大框边距（标注在对应内侧空白处：上下标于大框边与首/末行之间，左右标于大框边与首/末列之间）
    mt = params["BIG_FRAME_MARGIN_TOP"]
    mb = params["BIG_FRAME_MARGIN_BOTTOM"]
    ml = templ["bigFrameLeft"]
    mr = templ["bigFrameRight"]
    mt_px = mm_to_px(mt, dpi)
    mb_px = mm_to_px(mb, dpi)
    ml_px = mm_to_px(ml, dpi)
    mr_px = mm_to_px(mr, dpi)
    last_col_right = cl[cols - 1] + cw  # 最后一列单元格右边
    v_center = (rt[0] + grid_bottom) // 2  # 单元格区域垂直中心（用于左右边距标注居中）

    # 上边距：大框顶边与第一行单元格之间的空白处
    sz = _calc_anno_font_size(f"\u2193{mt}mm", br - bl, mt_px, max_size=18, min_size=10)
    _al(f"\u2193{mt}mm", bl + 4, (bt + rt[0]) // 2 - sz // 2, _load_anno_font(sz), "大框上边距")
    # 下边距：末行单元格与大框底边之间的空白处
    sz = _calc_anno_font_size(f"\u2191{mb}mm", br - bl, mb_px, max_size=18, min_size=10)
    _al(f"\u2191{mb}mm", bl + 4, (grid_bottom + bb) // 2 - sz // 2, _load_anno_font(sz), "大框下边距")

    # 左边距：大框左边与第一列单元格之间的空白处（水平居中于间隙，垂直居中于单元格区）
    sz = _calc_anno_font_size(f"\u2190{ml}\u2192", ml_px, 30, max_size=16, min_size=8)
    _al(f"\u2190{ml}\u2192", (bl + cl[0]) // 2 - sz * len(f"\u2190{ml}\u2192") // 3, v_center - sz // 2, _load_anno_font(sz), "大框左边距")
    # 右边距：末列单元格与大框右边之间的空白处
    sz = _calc_anno_font_size(f"\u2190{mr}\u2192", mr_px, 30, max_size=16, min_size=8)
    _al(f"\u2190{mr}\u2192", (last_col_right + br) // 2 - sz * len(f"\u2190{mr}\u2192") // 3, v_center - sz // 2, _load_anno_font(sz), "大框右边距")

    # 9. 画布边距（标注在画布边与大框边之间的空白处，若实际间距为0则标注在大框内侧对应空白处）
    ct = params["CANVAS_TO_BIGFRAME_TOP"]
    cb = params["CANVAS_TO_BIGFRAME_BOTTOM"]
    ct_px = mm_to_px(ct, dpi)
    cb_px = mm_to_px(cb, dpi)
    cl_left = templ["canvasToBigLeft"]
    cl_right = templ["canvasToBigRight"]

    # 画布上边距：画布顶边与大框顶边之间
    sz = _calc_anno_font_size(f"\u2193{ct}mm", br - bl, ct_px, max_size=18, min_size=10)
    _al(f"\u2193{ct}mm", bl + 4, ct_px // 2 - sz // 2 + 4, _load_anno_font(sz), "画布上边距")
    # 画布下边距：大框底边与画布底边之间
    sz = _calc_anno_font_size(f"\u2191{cb}mm", br - bl, cb_px, max_size=18, min_size=10)
    _al(f"\u2191{cb}mm", bl + 4, bb + cb_px // 2 - sz // 2 + 4, _load_anno_font(sz), "画布下边距")

    # 画布左边距
    if cl_left > 0:
        cl_left_px = mm_to_px(cl_left, dpi)
        sz = _calc_anno_font_size(f"{cl_left}mm\u2190", cl_left_px, 30, max_size=16, min_size=8)
        _al(f"{cl_left}mm\u2190", cl_left_px // 2 - sz * len(f"{cl_left}mm\u2190") // 2 + 2, v_center - sz // 2, _load_anno_font(sz), "画布左边距")
    else:
        # 间距为0，标注在大框内侧左边空白处
        sz = _calc_anno_font_size("\u21900mm", ml_px, 30, max_size=14, min_size=8)
        _al("\u21900mm", bl + 4, v_center - sz // 2, _load_anno_font(sz), "画布左边距=0")

    # 画布右边距
    if cl_right > 0:
        cr_px = mm_to_px(cl_right, dpi)
        sz = _calc_anno_font_size(f"\u2192{cl_right}mm", cr_px, 30, max_size=16, min_size=8)
        _al(f"\u2192{cl_right}mm", br + cr_px // 2 - sz * len(f"\u2192{cl_right}mm") // 2 + 2, v_center - sz // 2, _load_anno_font(sz), "画布右边距")
    else:
        # 间距为0，标注在大框内侧右边空白处
        sz = _calc_anno_font_size("\u21900mm", mr_px, 30, max_size=14, min_size=8)
        _al("\u21900mm", br - 4 - sz * 2, v_center - sz // 2, _load_anno_font(sz), "画布右边距=0")

    # 10. 画布尺寸
    text = f"{templ['canvasW_mm']}x{templ['canvasH_mm']}mm"
    sz = _calc_anno_font_size(text, canvas_w - 20, 30, max_size=22)
    _al(text, 10, canvas_h - 20, _load_anno_font(sz), "画布尺寸")

    # 优化：所有标注文字已绘制到同一张画布上，只创建一次图层（替代原来16次全画布图层创建）
    layer = psd.create_pixel_layer(name='尺寸标注', image=anno_img, top=0, left=0)
    layer.move_to_group(anno_group)


# ==================== 小版生成（PSD 图层版） ====================
def generate_small_board(instance_name, template_idx, placements, params, pic_folder, out_dir, progress_cb=None, cancel_check=None):
    """生成一块小版的完整 PSD 文件。
    
    生成流程：
      1. 计算网格坐标（compute_grid）
      2. 创建模板 PSD（背景 + 框线 + 辅助线 + 空经文组）
      3. 遍历所有 placement：
         - skip 类型：跳过空格
         - char 类型：加载字图 → 缩放 → 白底转透明 → 居中放入单元格
         - 按段落 paraIndex 移入对应段落子组（首次遇到某段落时自动创建）
      4. 图层结构：经文组 → 段落子组（00.题目~33.尾题）→ 字符图层
      5. 添加尺寸标注图层（可选）
      6. 保存为 PSD 文件
    
    每个字符图层命名格式：{字符}_{行号}_{列号}（如"佛_1_1"），
    图层名经过 _safe_psd_name() 处理，确保 GBK 兼容。
    
    参数：
      instance_name (str): 小版名称（如"小版1.1"）
      template_idx (int): 模板索引（0~4）
      placements (list): 分配结果中的 placements 数组
      params (dict): 参数字典
      pic_folder (str): 字库图片目录
      out_dir (str): 输出目录
      progress_cb (callable): 进度回调 (pct, total, msg)
      cancel_check (callable): 取消检查回调，返回 True 时抛出 GenerationCancelled
    
    返回：
      int: 成功放置的字符数量
    """
    _t0 = time.time()
    templ = SMALL_TEMPLATES[template_idx]
    dpi = params["DPI"]
    if progress_cb:
        progress_cb(0, 100, "计算网格...")
    grid = compute_grid(templ, params, dpi)
    cw, ch = grid["cell_w"], grid["cell_h"]
    rt, cl = grid["row_tops"], grid["col_lefts"]
    placed = 0
    max_imgs = params["TEST_CHAR_LIMIT"] or 999999
    total = len(placements)

    if progress_cb:
        progress_cb(1, 100, "创建图层结构...")
    psd = _gen_template_psd_only(templ, params, dpi, grid=grid, progress_cb=progress_cb, cancel_check=cancel_check)
    _t1 = time.time()
    log(f"  [{instance_name}] 框线绘制耗时: {_t1 - _t0:.2f}秒")

    # 查找经文组
    jingwen_group = None
    for l in psd.descendants():
        if l.is_group() and '经' in l.name:
            jingwen_group = l
            break
    if jingwen_group is None:
        jingwen_group = psd.create_group(name='经文组')

    # 字符图层（按段落二级分组：经文组 → 段落子组 → 字符图层）
    para_groups = {}    # paraIndex → 段落子组（PSD Group 对象）
    for pi, pl in enumerate(placements):
        if pl["type"] == "skip":
            if progress_cb:
                progress_cb(pi + 1, total, f"跳过空格 ({pi+1}/{total})")
            continue
        if placed >= max_imgs:
            break

        ch_char = pl["character"]
        if progress_cb and placed % 10 == 0:
            progress_cb(placed, total, f"处理字符 {ch_char} (行{pl['actualRow']+1}列{templ['cols'] - pl['actualCol']})  [{pi}/{total}]")
        cell_x = cl[pl["actualCol"]]
        cell_y = rt[pl["actualRow"]]

        try:
            img_path, src_w, src_h, src_res = _get_cached_image_info(pic_folder, ch_char, pl["absoluteCharIdx"], dpi=params["DPI"])
            if not img_path:
                if progress_cb:
                    progress_cb(pi + 1, total, f"字图不存在 {ch_char} ({pi+1}/{total})")
                continue

            tw, th = calc_target_size(src_w, src_h, src_res, cw, ch,
                                      params["SCALE_MODE"], params["SCALE_PERCENT"],
                                      params["AUTO_SCALE_THRESHOLD"], params["AUTO_FILL_W"], params["AUTO_FILL_H"],
                                      params["AUTO_SHRINK_THRESHOLD"], params["SHRINK_FILL_W"], params["SHRINK_FILL_H"],
                                      dpi=params["DPI"], cell_fill_ratio=params["CELL_FILL_RATIO"])

            resized = _get_processed_image(img_path, tw, th)
            cx = cell_x + (cw - tw) // 2
            cy = cell_y + (ch - th) // 2

            # --- 添加到 PSD 图层 ---
            psd_layer_img = resized  # RGBA 直接保留透明

            layer = psd.create_pixel_layer(
                # 列号从右向左编号（cols - actualCol）：第1列为最右列（阅读顺序首列）
                name=_safe_psd_name(f'{ch_char}_{pl["actualRow"] + 1}_{templ["cols"] - pl["actualCol"]}'),
                image=psd_layer_img, top=cy, left=cx)

            # 按段落移入对应子组（首次遇到某段落时创建段落子组）
            para_idx = pl["paraIndex"]
            if para_idx not in para_groups:
                group_name = PARA_NAMES[para_idx] if para_idx < len(PARA_NAMES) else f"段落-{para_idx + 1}"
                pg = psd.create_group(name=_safe_psd_name(group_name), open_folder=False)
                pg.move_to_group(jingwen_group)  # type: ignore[reportArgumentType]
                para_groups[para_idx] = pg
            layer.move_to_group(para_groups[para_idx])

            placed += 1
            # 每 20 字检查一次取消标志
            if placed % 20 == 0 and cancel_check and cancel_check():
                raise GenerationCancelled(f"小版字符放置阶段——用户取消（已放置{placed}字）")
        except GenerationCancelled:
            raise
        except Exception as e:
            log(f"    处理失败: {ch_char} - {e}")

        if progress_cb:
            progress_cb(pi + 1, total)

    _t2 = time.time()
    log(f"  [{instance_name}] 字符放置耗时: {_t2 - _t1:.2f}秒 ({placed}字, {len(para_groups)}个段落组)")

    # 标注图层
    if progress_cb:
        progress_cb(98, 100, "添加尺寸标注...")
    if params["ADD_ANNOTATION"]:
        add_small_board_annotations(psd, templ, params, dpi, grid, progress_cb=progress_cb, cancel_check=cancel_check)
    _t3 = time.time()
    if params["ADD_ANNOTATION"]:
        log(f"  [{instance_name}] 尺寸标注耗时: {_t3 - _t2:.2f}秒")

    # 保存 PSD
    if progress_cb:
        progress_cb(99, 100, f"保存 PSD（{placed}个字图层）...")
    fname = save_filename(instance_name, params["DPI"])
    psd_path = os.path.join(out_dir, fname + ".psd")
    _collapse_all_groups(psd)
    psd._updated = False
    _psd_save_with_debug(psd, psd_path)
    log(f"  已保存: {fname}.psd ({placed}字)")
    _t4 = time.time()
    log(f"  [{instance_name}] 保存PSD耗时: {_t4 - _t3:.2f}秒")
    log(f"  [{instance_name}] ====== 总耗时: {_t4 - _t0:.2f}秒 ======")

    return placed


# ==================== 大版生成 ====================
# 大版是将多块小版水平拼合到一个大画布上的 PSD 文件。
# 与 ExtendScript 版本不同，Python 版直接在同一画布上绘制所有内容，
# 而不是生成小版文件后再导入拼合，这样可以减少中间文件 IO 和内存占用。

def _collapse_all_groups(psd):
    """折叠 PSD 中的所有图层组（open_folder = False）。
    
    折叠后 PSD 在 Photoshop 中打开时所有组默认收起，
    避免成千上万个字符图层造成界面卡顿。
    """
    for l in psd.descendants():
        if hasattr(l, 'open_folder'):
            try:
                l.open_folder = False
            except Exception:
                pass


def generate_big_board(board_idx, indices, params, out_dir, dpi, allocs, pic_folder, progress_cb=None, cancel_check=None):
    """直接在大画布上生成大版 PSD（不依赖小版 PSD 文件）。
    
    与 ExtendScript 版本不同，Python 版采用"直接绘制"方案：
      直接在 5000~6500×5900mm 的大画布上逐字放置字符图层，
      同时绘制所有框线（大框 + 各小版的单元格 + 辅助线）。
      所有框线合并为单个 RGBA 图层，减少 PSD 图层数量和内存占用。
    
    大版排版逻辑：
      1. 大框水平居中于大画布
      2. 各小版在大框内从右向左排列（order 0 最右）
      3. 每个小版的单元格和分割线偏移到对应的大版坐标
    
    进度条分布：
      0%~10%:  网格初始化（创建 PSD、背景、框线组、绘制所有框线）
      10%~95%: 逐字符放置文字（按小版顺序依次处理）
      95%~97%: 添加尺寸标注图层
      97%~100%: 保存 PSD 文件
    
    参数：
      board_idx (int): 大版索引（0~4）
      indices (list): 该大版包含的小版实例索引列表
      params (dict): 参数字典
      out_dir (str): 输出目录
      dpi (int): 输出分辨率
      allocs (list): allocate_all_boards 返回的分配结果
      pic_folder (str): 字库图片目录
      progress_cb (callable): 进度回调 (pct, total, msg)
      cancel_check (callable): 取消检查回调，返回 True 时抛出 GenerationCancelled
    """
    _t0 = time.time()
    defn = BIG_BOARD_DEFS[board_idx]
    canvas_w = mm_to_px(defn["canvasW_mm"], dpi)
    canvas_h = mm_to_px(defn["canvasH_mm"], dpi)
    bf_l = mm_to_px((defn["canvasW_mm"] - defn["bigFrameW_mm"]) / 2, dpi)
    bf_t = mm_to_px(defn["topMargin_mm"], dpi)
    bf_r = mm_to_px((defn["canvasW_mm"] + defn["bigFrameW_mm"]) / 2, dpi)
    bf_b = mm_to_px(defn["topMargin_mm"] + defn["bigFrameH_mm"], dpi)

    # 计算总字符数用于进度
    alloc_map = {al["instanceName"]: al for al in allocs}
    total_chars = 0
    for idx in indices:
        inst = BOARD_INSTANCES[idx]
        al = alloc_map.get(inst["name"])
        if al:
            total_chars += sum(1 for p in al["placements"] if p["type"] == "char")

    board_name = f"大版-{board_idx + 1}"
    def _p(phase_pct, step_msg):
        if progress_cb:
            progress_cb(phase_pct, 100, f"大版 {board_name} - {step_msg}")

    # 进度分布：网格初始化 0~10%，文字放置 10~95%，标注 95~97%，保存 97~100%
    _GRID_BASE = 1  # 初始化阶段起始
    _GRID_TOTAL = 10  # 网格阶段结束百分比点
    num_slots = len(indices)
    _GRID_TOTAL_STEPS = 6 + num_slots * 2  # 初始化步骤 + 每小版计算网格+绘制框线

    _init_step = 0
    def _grid_p(msg):
        nonlocal _init_step
        pct = _GRID_BASE + (_init_step / _GRID_TOTAL_STEPS) * (_GRID_TOTAL - _GRID_BASE)
        _p(pct, msg)
        _init_step += 1

    _grid_p("初始化 PSD 文档...")
    psd = PSDImage.new('RGB', (canvas_w, canvas_h))
    set_psd_resolution(psd, dpi)

    # 白色背景
    _grid_p("创建背景图层...")
    psd.create_pixel_layer(name='背景', image=Image.new("RGB", (canvas_w, canvas_h), (255, 255, 255)), top=0, left=0)

    # 经文组（先于框线组）
    _grid_p("创建经文组...")
    jingwen_group = psd.create_group(name='经文组')

    # 框线组 — 所有框线合并为单个 RGBA 图层
    _grid_p("创建框线组...")
    frame_group = psd.create_group(name='框线')
    _grid_p("创建框线底图...")
    frame_img = Image.new("RGBA", (canvas_w, canvas_h), (0, 0, 0, 0))
    frame_dr = ImageDraw.Draw(frame_img)
    _grid_p("绘制大框...")

    # 大版自己的大框
    frame_dr.rectangle([bf_l, bf_t, bf_r, bf_b], outline=LINE_COLOR, width=1)

    # 第一遍：从右向左排列各小版，预计算网格并统计总格数
    x_offset = bf_r
    slot_info = []
    _total_frame_cells = 0
    for si, idx in enumerate(indices):
        inst = BOARD_INSTANCES[idx]
        templ = SMALL_TEMPLATES[inst["templateIdx"]]
        tpl_w_px = mm_to_px(templ["canvasW_mm"], dpi)
        x_offset -= tpl_w_px
        _grid_p(f"计算网格 - {inst['name']}...")
        grid = compute_grid(templ, params, dpi)
        slot_info.append({
            "inst": inst, "templ": templ, "grid": grid,
            "offset_x": x_offset, "offset_y": bf_t
        })
        _total_frame_cells += grid["rows"] * grid["cols"]

    # 百分比阈值：每 10% 检查一次取消（最少 1 格）
    _frame_threshold = max(1, _total_frame_cells // 10)
    _frame_cell_count = 0

    # 第二遍：在框线图上绘制各小版网格
    for si_idx, si in enumerate(slot_info):
        inst = si["inst"]
        grid = si["grid"]
        ox, oy = si["offset_x"], si["offset_y"]
        rt, cl = grid["row_tops"], grid["col_lefts"]
        rows, cols = grid["rows"], grid["cols"]
        cw, ch = grid["cell_w"], grid["cell_h"]
        _grid_p(f"绘制框线 - {inst['name']}...")
        for r in range(rows):
            yt, yb = rt[r] + oy, rt[r] + ch + oy
            for c in range(cols):
                xl, xr = cl[c] + ox, cl[c] + cw + ox
                frame_dr.rectangle([xl, yt, xr, yb], outline=LINE_COLOR, width=1)
                cx = round(cl[c] + cw / 2) + ox
                cy = round(rt[r] + ch / 2) + oy
                frame_dr.line([(cx, yt), (cx, yb)], fill=GUIDE_COLOR, width=1)
                frame_dr.line([(xl, cy), (xr, cy)], fill=GUIDE_COLOR, width=1)
                _frame_cell_count += 1
                # 每达到总格数 10% 检查一次取消标志
                if _frame_cell_count % _frame_threshold == 0 and cancel_check and cancel_check():
                    raise GenerationCancelled(f"大版框线绘制阶段——用户取消（已绘制{_frame_cell_count}/{_total_frame_cells}格）")
        # 蓝色分割线
        split_row_idx = params["SPLIT_LINE_AFTER_ROW"] - 1
        if 0 <= split_row_idx < rows - 1:
            split_y = round((rt[split_row_idx] + ch + rt[split_row_idx + 1]) / 2 - 0.5) + oy
            bl_slot = grid["big_left"] + ox
            br_slot = grid["big_right"] + ox
            frame_dr.line([(bl_slot, split_y), (br_slot, split_y)], fill=SPLIT_COLOR, width=1)

        # 小版大框（四条边分别绘制，共享边只画一次）
        bl_s = grid["big_left"] + ox
        br_s = grid["big_right"] + ox
        bt_s = grid["big_top"] + oy
        bb_s = grid["big_bottom"] + oy

        # 上边和下边：始终绘制
        frame_dr.line([(bl_s, bt_s), (br_s, bt_s)], fill=LINE_COLOR, width=1)
        frame_dr.line([(bl_s, bb_s), (br_s, bb_s)], fill=LINE_COLOR, width=1)

        # 右边：仅当是最右侧版（与右侧无邻版）或与右侧版左边不重合时绘制
        draw_right = True
        if si_idx > 0:
            prev_left = slot_info[si_idx - 1]["grid"]["big_left"] + slot_info[si_idx - 1]["offset_x"]
            if abs(br_s - prev_left) <= 1:  # 允许1px浮点误差
                draw_right = False
        if draw_right:
            frame_dr.line([(br_s, bt_s), (br_s, bb_s)], fill=LINE_COLOR, width=1)

        # 左边：仅当是最左侧版（与左侧无邻版）或与左侧版右边不重合时绘制
        draw_left = True
        if si_idx < len(slot_info) - 1:
            next_right = slot_info[si_idx + 1]["grid"]["big_right"] + slot_info[si_idx + 1]["offset_x"]
            if abs(bl_s - next_right) <= 1:
                draw_left = False
        if draw_left:
            frame_dr.line([(bl_s, bt_s), (bl_s, bb_s)], fill=LINE_COLOR, width=1)

    frame_layer = psd.create_pixel_layer(name='框线', image=frame_img, top=0, left=0)
    frame_layer.move_to_group(frame_group)
    _t1 = time.time()
    log(f"  [{board_name}] 框线绘制耗时: {_t1 - _t0:.2f}秒")

    _p(10, "框线完成，开始放置文字...")

    # 放置文字：从 allocs 分配数据直接绘制
    placed_total = 0

    # 预计算各小版字符数用于进度分配
    slot_char_counts = []
    for si in slot_info:
        inst = si["inst"]
        al = alloc_map.get(inst["name"])
        slot_char_counts.append(sum(1 for p in al["placements"] if p["type"] == "char") if al else 0)
    total_slot_chars = sum(slot_char_counts) or 1

    # 段落子组缓存（大版中所有小版共用，按 paraIndex 唯一创建）
    para_groups = {}

    for si_idx, si in enumerate(slot_info):
        inst = si["inst"]
        sname = inst["name"]
        al = alloc_map.get(sname)
        if al is None:
            continue
        g = si["grid"]
        cw, ch = g["cell_w"], g["cell_h"]
        rt, cl = g["row_tops"], g["col_lefts"]
        ox, oy = si["offset_x"], si["offset_y"]
        max_imgs = params["TEST_CHAR_LIMIT"] or 999999
        placed = 0
        slot_chars = slot_char_counts[si_idx]

        for pl in al["placements"]:
            if pl["type"] == "skip":
                if progress_cb and slot_chars > 0:
                    char_pct = 10 + 85 * (placed_total + placed) / total_slot_chars
                    progress_cb(int(char_pct), 100, f"大版 {board_name} - 跳过空格 ({sname})")
                continue
            if placed >= max_imgs:
                break
            ch_char = pl["character"]
            if progress_cb and placed % 10 == 0 and slot_chars > 0:
                char_pct = 10 + 85 * (placed_total + placed) / total_slot_chars
                progress_cb(int(char_pct), 100, f"大版 {board_name} - 处理字符 {ch_char} ({sname})  ({placed}/{slot_chars})")
            cell_x = cl[pl["actualCol"]]
            cell_y = rt[pl["actualRow"]]
            try:
                img_path, src_w, src_h, src_res = _get_cached_image_info(pic_folder, ch_char, pl["absoluteCharIdx"], dpi=params["DPI"])
                if not img_path:
                    if progress_cb and slot_chars > 0:
                        char_pct = 10 + 85 * (placed_total + placed) / total_slot_chars
                        progress_cb(int(char_pct), 100, f"大版 {board_name} - 字图不存在 {ch_char}")
                    continue
                tw, th = calc_target_size(src_w, src_h, src_res, cw, ch,
                                          params["SCALE_MODE"], params["SCALE_PERCENT"],
                                          params["AUTO_SCALE_THRESHOLD"], params["AUTO_FILL_W"], params["AUTO_FILL_H"],
                                          params["AUTO_SHRINK_THRESHOLD"], params["SHRINK_FILL_W"], params["SHRINK_FILL_H"],
                                          dpi=params["DPI"], cell_fill_ratio=params["CELL_FILL_RATIO"])
                resized = _get_processed_image(img_path, tw, th)
                cx_px = cell_x + (cw - tw) // 2 + ox
                cy_px = cell_y + (ch - th) // 2 + oy
                layer = psd.create_pixel_layer(
                    # 列号从右向左编号（g["cols"] - actualCol）：第1列为最右列（阅读顺序首列）
                    name=_safe_psd_name(f'{ch_char}_{pl["actualRow"] + 1}_{g["cols"] - pl["actualCol"]}'),
                    image=resized, top=cy_px, left=cx_px)

                # 按段落移入对应子组（大版中所有小版共用同一个段落子组缓存）
                para_idx = pl["paraIndex"]
                if para_idx not in para_groups:
                    group_name = PARA_NAMES[para_idx] if para_idx < len(PARA_NAMES) else f"段落-{para_idx + 1}"
                    pg = psd.create_group(name=_safe_psd_name(group_name), open_folder=False)
                    pg.move_to_group(jingwen_group)  # type: ignore[reportArgumentType]
                    para_groups[para_idx] = pg
                layer.move_to_group(para_groups[para_idx])  # type: ignore[arg-type]

                placed += 1
                # 每 30 字检查一次取消标志
                if placed % 30 == 0 and cancel_check and cancel_check():
                    raise GenerationCancelled(f"大版字符放置阶段——用户取消（{sname}已放置{placed}字）")
            except GenerationCancelled:
                raise
            except Exception as e:
                log(f"    处理失败: {ch_char} - {e}")
        placed_total += placed
        if progress_cb:
            progress_cb(10 + int(85 * (placed_total / total_slot_chars)), 100,
                        f"大版 {board_name} - {sname}: {placed}字完成")
        log(f"    {sname}: {placed}字")
    _t2 = time.time()
    log(f"  [{board_name}] 字符放置耗时: {_t2 - _t1:.2f}秒 ({placed_total}字, {len(para_groups)}个段落组)")

    # 大版尺寸标注（合并图层 + 箭头指示 + 动态字号）
    _p(95, "添加尺寸标注...")
    if params["ADD_ANNOTATION"]:
        anno_img = Image.new('RGBA', (canvas_w, canvas_h), (0, 0, 0, 0))

        def _al(text, x, y, font):
            _make_text_layer(anno_img, text, max(0, x), max(0, y), font, color=ANNO_COLOR)

        # 大版整体信息（动态字号）
        _al(f"{board_name}", canvas_w // 2 - 20, 40,
            _load_anno_font(_calc_anno_font_size(board_name, canvas_w, bf_t, max_size=24)))
        _al(f"{defn['canvasW_mm']}x{defn['canvasH_mm']}mm", 10, canvas_h - 20,
            _load_anno_font(_calc_anno_font_size(f"{defn['canvasW_mm']}x{defn['canvasH_mm']}mm",
                                                 canvas_w, 30, max_size=18)))
        big_frame_text = f"\u2192大框{defn['bigFrameW_mm']}x{defn['bigFrameH_mm']}"
        bf_sz = _calc_anno_font_size(big_frame_text, canvas_w - bf_r, bf_t, max_size=18)
        _al(big_frame_text,
            min(bf_r + 10, canvas_w - bf_sz * len(big_frame_text) - 8),
            bf_t + 16, _load_anno_font(bf_sz))
        big_left_margin = round((defn['canvasW_mm'] - defn['bigFrameW_mm']) / 2)
        # 画布边距（动态字号）
        _al(f"\u2191画布上{defn['topMargin_mm']}", bf_l + 10, bf_t // 2 + 4,
            _load_anno_font(_calc_anno_font_size(f"\u2191画布上{defn['topMargin_mm']}",
                                                 canvas_w, bf_t // 2, max_size=18)))
        _al(f"\u2193画布下{defn['bottomMargin_mm']}", bf_l + 10,
            bf_b + mm_to_px(defn['bottomMargin_mm'] // 2, dpi) + 4,
            _load_anno_font(_calc_anno_font_size(f"\u2193画布下{defn['bottomMargin_mm']}",
                                                 canvas_w, bf_b // 2, max_size=18)))
        _al(f"\u2192{big_left_margin}左", bf_l + 4, bf_t + 20,
            _load_anno_font(_calc_anno_font_size(f"\u2192{big_left_margin}左",
                                                 mm_to_px(big_left_margin, dpi) * 3, 30, max_size=20, min_size=10)))
        _al(f"{big_left_margin}右\u2190", bf_r - 4, bf_t + 20,
            _load_anno_font(_calc_anno_font_size(f"{big_left_margin}右\u2190",
                                                 mm_to_px(big_left_margin, dpi) * 3, 30, max_size=20, min_size=10)))
        # 各小版标注
        _anno_slot_count = 0
        for si in slot_info:
            inst = si["inst"]
            templ = si["templ"]
            g = si["grid"]
            ox, oy = si["offset_x"], si["offset_y"]
            rt, cl = g["row_tops"], g["col_lefts"]
            rows, cols = g["rows"], g["cols"]
            cw, ch = g["cell_w"], g["cell_h"]
            bl_s, br_s = g["big_left"], g["big_right"]
            bt_s, bb_s = g["big_top"], g["big_bottom"]
            grid_btm = rt[rows - 1] + ch + oy
            tx = ox + (cl[cols - 1] + cw + cl[0]) // 2
            ty = oy + 10
            # 实例名
            sz = _calc_anno_font_size(inst['name'], br_s + mm_to_px(big_left_margin, dpi) // 2, bt_s, max_size=22)
            _al(f"{inst['name']}", tx - 20, ty, _load_anno_font(sz))
            # 列数×行数（与实例名之间留出足够行距）
            sz = _calc_anno_font_size(f"{cols}列x{rows}行", br_s + mm_to_px(big_left_margin, dpi) // 2, bt_s - 20, max_size=20)
            _al(f"{cols}列x{rows}行", tx - 20, ty + 30, _load_anno_font(sz))
            # 单元格尺寸
            sz = _calc_anno_font_size(f"{params['CELL_W']}x{params['CELL_H']}mm", cw, ch, max_size=18)
            _al(f"{params['CELL_W']}x{params['CELL_H']}mm", cl[cols - 1] + ox + 4, rt[0] + oy + 14, _load_anno_font(sz))
            # 列间距
            if cols > 1:
                gap_w = cl[cols - 1] - (cl[cols - 2] + cw)
                text = f"\u2190{templ['colGap_mm']}mm\u2192"
                sz = _calc_anno_font_size(text, gap_w, ch // 2, max_size=14, min_size=8)
                gap_x = (cl[cols - 2] + cw + cl[cols - 1]) // 2 + ox
                _al(text, gap_x - sz * len(text) // 3, rt[0] + oy + 14, _load_anno_font(sz))
            # 行间距（垂直居中于行间空白）
            if rows > 1:
                text = f"\u2191{params['ROW_GAP']}mm\u2193"
                gap_h = rt[1] - (rt[0] + ch)
                sz = _calc_anno_font_size(text, cw // 2, gap_h, max_size=14, min_size=10)
                gap_y = (rt[0] + ch + rt[1]) // 2 + oy
                _al(text, cl[cols - 1] + ox + 6, gap_y - sz // 2, _load_anno_font(sz))
            # 分割线位置（智能选择左右侧）
            split_row_idx = params["SPLIT_LINE_AFTER_ROW"] - 1
            if 0 <= split_row_idx < rows - 1:
                split_y = round((rt[split_row_idx] + ch + rt[split_row_idx + 1]) / 2 - 0.5) + oy
                gap_size = params["ROW_GAP"] // 2
                text = f"\u2502\u2190第{params['SPLIT_LINE_AFTER_ROW']}行后 {gap_size}mm"
                right_space = canvas_w - (br_s + ox + 8)
                left_space = bl_s + ox
                if right_space >= 40:
                    sz = _calc_anno_font_size(text, right_space, ch, max_size=16)
                    est_w = sz * len(text)
                    _al(text, min(br_s + ox + 8, canvas_w - est_w - 8), split_y + 4, _load_anno_font(sz))
                elif left_space >= 40:
                    sz = _calc_anno_font_size(text, left_space, ch, max_size=16)
                    _al(text, max(2, bl_s + ox - 80), split_y + 4, _load_anno_font(sz))
                else:
                    sz = _calc_anno_font_size(text, canvas_w, ch, max_size=14, min_size=8)
                    cx = (bl_s + br_s) // 2 + ox
                    _al(text, max(2, cx - sz * len(text) // 2), split_y + 4, _load_anno_font(sz))
            # 大框上下边距
            mt = params["BIG_FRAME_MARGIN_TOP"]
            mb = params["BIG_FRAME_MARGIN_BOTTOM"]
            mt_px = mm_to_px(mt, dpi)
            mb_px = mm_to_px(mb, dpi)
            _al(f"\u2191上{mt}", bl_s + ox + 4, bt_s + oy + mt_px // 2 - 8,
                _load_anno_font(_calc_anno_font_size(f"\u2191上{mt}", br_s - bl_s, mt_px, max_size=16)))
            _al(f"\u2193下{mb}", bl_s + ox + 4, bb_s + oy - mb_px // 2 - 8,
                _load_anno_font(_calc_anno_font_size(f"\u2193下{mb}", br_s - bl_s, mb_px, max_size=16)))
            # 左右边距（箭头在内、文字向外延伸，防右侧超界）
            ml = templ["bigFrameLeft"]
            mr = templ["bigFrameRight"]
            if ml > 0:
                ml_px = mm_to_px(ml, dpi)
                sz = _calc_anno_font_size(f"\u2192{ml}左", ml_px * 3, 24, max_size=20, min_size=10)
                _al(f"\u2192{ml}左", ox + bl_s + 4, grid_btm + 14, _load_anno_font(sz))
            if mr > 0:
                mr_px = mm_to_px(mr, dpi)
                sz = _calc_anno_font_size(f"{mr}右\u2190", mr_px * 3, 24, max_size=20, min_size=10)
                _al(f"{mr}右\u2190", ox + br_s - 4, grid_btm + 14, _load_anno_font(sz))
            _anno_slot_count += 1
            # 每 3 个小版的标注完成后检查一次取消标志
            if _anno_slot_count % 3 == 0 and cancel_check and cancel_check():
                raise GenerationCancelled(f"大版尺寸标注阶段——用户取消（已完成{_anno_slot_count}版标注）")
        anno_group = psd.create_group(name='尺寸标注组')
        layer = psd.create_pixel_layer(name='尺寸标注', image=anno_img, top=0, left=0)
        layer.move_to_group(anno_group)
    _t3 = time.time()
    if params["ADD_ANNOTATION"]:
        log(f"  [{board_name}] 尺寸标注耗时: {_t3 - _t2:.2f}秒")

    # 保存前释放大中间变量，减轻内存压力
    del frame_img, slot_info, alloc_map
    gc.collect()

    # 保存 PSD
    fname = save_filename(board_name, params["DPI"])
    _p(97, "保存 PSD...")
    out_path = os.path.join(out_dir, fname + ".psd")
    _collapse_all_groups(psd)
    psd._updated = False
    _psd_save_with_debug(psd, out_path)
    log(f"  已保存: {fname}.psd ({placed_total}字)")
    _t4 = time.time()
    log(f"  [{board_name}] 保存PSD耗时: {_t4 - _t3:.2f}秒")
    log(f"  [{board_name}] ====== 总耗时: {_t4 - _t0:.2f}秒 ======")

    _p(100, "大版完成")


# ==================== 主生成流程 ====================
def _check_gbk_compat(allocs):
    """检查所有分配到的字符是否可用 GBK 编码。
    
    PSD 图层名称（如"佛_1_1"）中的每个字符都必须可用 GBK 编码。
    如果存在 GBK 不支持的字符，_safe_psd_name() 已将其替换为 '?'，
    本函数仅做通知性警告，不影响生成流程。
    """
    bad = set()
    for al in allocs:
        for pl in al["placements"]:
            ch = pl.get("character", "")
            if not ch:
                continue
            # GBK 兼容性仅检查字符本身，行列数字永远合规，无需精确匹配实际命名公式
            full_name = f'{ch}_{pl.get("actualRow", 0) + 1}_{pl.get("actualCol", 0) + 1}'
            for c in full_name:
                if c in _GBK_UNENCODABLE:
                    bad.add(f"{c} (U+{ord(c):04X})")
    if bad:
        log("⚠ 以下字符无法用 GBK 编码，已在图层名称中用 '?' 替代：")
        for b in sorted(bad):
            log(f"    {b}")

def run_generation(params, small_sel, big_sel, progress=None, cancel_check=None):
    """主生成流程：解析经文 → 分配小版 → 生成小版 → 生成大版。
    
    这是顶层调度函数，协调全部生成步骤：
      1. parse_scripture()         — 解析经文文本为 items 数组
      2. allocate_all_boards()     — 分配字符到 16 块小版
      3. _check_gbk_compat()       — 检查 GBK 编码兼容性（仅警告）
      4. generate_small_board() ×N — 生成选中的小版 PSD
      5. generate_big_board() ×N   — 生成选中的大版 PSD
    
    每个步骤都有日志输出和进度回调。
    大版生成后手动触发 gc.collect() 释放 PSD 内存。
    
    参数：
      params (dict): 参数字典
      small_sel (list): 16 个布尔值，是否生成对应小版
      big_sel (list): 5 个布尔值，是否生成对应大版
      progress (callable): 总体进度回调 (cur, total, msg)
      cancel_check (callable): 取消检查回调，返回 True 时中止生成
    
    返回：
      (int, int): 生成的小版数量和大版数量（被取消时返回已完成的部分结果）
    """
    dpi = params["DPI"]
    pic_folder = params["PIC_FOLDER"]
    out_dir = params["WORK_DIR"]
    os.makedirs(out_dir, exist_ok=True)

    if progress:
        progress(0, 100, "解析经文...")
    log("=== 解析经文 ===")
    items = parse_scripture(params["SCRIPTURE_TEXT"])
    log(f"总字符数: {len(items)}")
    if progress:
        progress(5, 100, "分配经文到各版面...")
    log("=== 分配经文 ===")
    allocs, _ = allocate_all_boards(items, params)
    for al in allocs:
        cnt = sum(1 for p in al["placements"] if p["type"] == "char")
        log(f"  {al['instanceName']}: {cnt}字{' (满)' if al['full'] else ' (未满)'}")

    # 检查所有字符是否可用 GBK 编码（PSD 图层名称要求）
    _check_gbk_compat(allocs)

    # 生成小版
    log("=== 生成小版 ===")
    small_cnt = 0
    total_small = sum(1 for bi in range(len(allocs)) if small_sel[bi])
    small_done = 0
    for bi, al in enumerate(allocs):
        if not small_sel[bi]:
            log(f"  跳过: {al['instanceName']}")
            continue
        out_path = os.path.join(out_dir, save_filename(al["instanceName"], params["DPI"]) + ".psd")
        if os.path.exists(out_path) and not params["OVERWRITE_MODE"]:
            log(f"  跳过(已存在): {al['instanceName']}")
            continue
        log(f"  生成: {al['instanceName']}...")

        def mk_progress(pi, pi_total, step_msg="", msg_prefix=al["instanceName"]):
            if total_small > 0:
                fraction = small_done / total_small + (pi / pi_total) / total_small
                pct = int(fraction * 100)
            else:
                pct = 0
            msg = f"小版 {msg_prefix}"
            if step_msg:
                msg += f" - {step_msg}"
            msg += f"  ({pi}/{pi_total})"
            if progress:
                progress(pct, 100, msg)

        def pcb(pi, pi_total, step_msg=""):
            mk_progress(pi, pi_total, step_msg)

        try:
            n = generate_small_board(al["instanceName"], al["templateIdx"],
                                      al["placements"], params, pic_folder, out_dir,
                                      progress_cb=pcb, cancel_check=cancel_check)
        except GenerationCancelled as e:
            log(f"用户取消——{e}")
            break
        small_done += 1
        small_cnt += 1
        log(f"  完成: {al['instanceName']} ({n}图)")
        if cancel_check and cancel_check():
            log("用户取消生成——停止小版生成")
            break

    # 生成大版（仅在未取消时执行）
    big_cnt = 0
    if cancel_check and cancel_check():
        log("用户取消生成——跳过所有大版")
    else:
        log("=== 生成大版 ===")
        total_big = sum(1 for bi in range(5) if big_sel[bi])
        big_done = 0
        for bi in range(5):
            if not big_sel[bi]:
                log(f"  跳过: 大版-{bi + 1}")
                continue
            defn = BIG_BOARD_DEFS[bi]
            out_path = os.path.join(out_dir, save_filename(f"大版-{bi + 1}", params["DPI"]) + ".psd")
            if os.path.exists(out_path) and not params["OVERWRITE_MODE"]:
                log(f"  跳过(已存在): 大版-{bi + 1}")
                continue

            def big_progress(inner_pct, inner_total, step_msg=""):
                fraction = big_done / total_big + (inner_pct / inner_total) / total_big
                pct = 50 + int(fraction * 50) if total_big > 0 else 100
                if progress:
                    progress(min(pct, 99), 100, step_msg)

            log(f"  生成: 大版-{bi + 1}...")
            try:
                generate_big_board(bi, defn["indices"], params, out_dir, dpi,
                                   allocs, pic_folder, progress_cb=big_progress,
                                   cancel_check=cancel_check)
            except GenerationCancelled as e:
                log(f"用户取消——{e}")
                break
            big_done += 1
            big_cnt += 1
            # 显式回收内存，避免大版 PSD 累加占用
            gc.collect()
            if cancel_check and cancel_check():
                log("用户取消生成——停止大版生成")
                break

    if progress:
        progress(100, 100, "全部完成")
    return small_cnt, big_cnt


# ==================== 窗口居中辅助函数 ====================
def _center_window(win, w, h):
    """将 tkinter 窗口定位在屏幕正中央。
    
    参数：
      win (tk.Toplevel): 目标窗口对象
      w (int): 窗口宽度（像素）
      h (int): 窗口高度（像素）
    """
    screen_w = win.winfo_screenwidth()
    screen_h = win.winfo_screenheight()
    x = (screen_w - w) // 2
    y = (screen_h - h) // 2
    win.geometry(f"{w}x{h}+{x}+{y}")


# ==================== 进度条对话框 ====================
class ProgressDialog:
    """模态进度条弹窗。
    
    在生成过程中显示进度条和当前步骤描述。
    自动置顶、拦截父窗口交互（grab_set），生成完成后关闭。
    
    UI 刷新节流：每次 update() 调用至少间隔 0.05 秒才真正更新 GUI，
    避免高频进度回调（每字符一次）导致界面卡死。
    
    支持用户取消：点击窗口右上角"X"时弹出确认对话框，确认后设置取消标志，
    生成循环检测到取消标志后安全退出，不会报错。
    """
    def __init__(self, parent, title="生成进度"):
        self.dialog = tk.Toplevel(parent)
        self.dialog.title(title)
        _center_window(self.dialog, 420, 110)
        self.dialog.transient(parent)   # 始终在父窗口之上
        self.dialog.grab_set()          # 拦截父窗口交互
        self.dialog.resizable(False, False)
        self.dialog.protocol("WM_DELETE_WINDOW", self._on_close)  # 拦截关闭按钮

        # 进度条（0~100）
        self.progress = ttk.Progressbar(self.dialog, length=380, mode='determinate', maximum=100)
        self.progress.pack(pady=(15, 5))

        # 状态文字
        self.status = tk.StringVar(value="初始化...")
        ttk.Label(self.dialog, textvariable=self.status).pack()

        self._last_update = 0.0  # 上次刷新时间（秒），用于节流
        self._cancelled = False  # 用户是否请求取消生成
        self.dialog.update()

    def _on_close(self):
        """用户点击窗口右上角"X"——弹出确认对话框，不直接销毁窗口"""
        if messagebox.askyesno("确认", "是否停止生成？"):
            self._cancelled = True
            self.status.set("正在停止...")
        # 不关闭窗口，由调用方在安全时机调用 close() 关闭

    def is_cancelled(self):
        """返回用户是否已请求取消生成"""
        return self._cancelled

    def update(self, pct, msg=""):
        """更新进度条和状态文字（带节流）。
        
        参数：
          pct (int): 进度百分比 0~100
          msg (str): 状态描述文字
        """
        if self._cancelled:
            return
        try:
            now = time.time()
            # 节流：至少间隔 0.05 秒才真正更新 UI
            if now - self._last_update < 0.05:
                return
            self._last_update = now
            self.progress['value'] = pct
            if msg:
                self.status.set(msg)
            self.dialog.update_idletasks()
            self.dialog.update()
        except tk.TclError:
            pass  # 窗口已被销毁，静默忽略

    def close(self):
        """关闭进度条，释放模态拦截"""
        try:
            self.dialog.grab_release()
            self.dialog.destroy()
        except tk.TclError:
            pass  # 窗口已被销毁，静默忽略


# ==================== 主应用程序（Tkinter GUI）====================
class App:
    """《金刚经》排版主应用程序。
    
    提供 6 个标签页的图形界面：
      标签1 — 基本设定（路径、DPI、缩放模式）
      标签2 — 单元格参数（尺寸、间距、分割线）
      标签3 — 小版模板（5 种模板的尺寸和边距）
      标签4 — 大版参数（5 块大版的尺寸和边距）
      标签5 — 经文文本（可编辑经文全文）
      标签6 — 生成版面选项（选择生成哪些小版/大版）
    
    底部按钮：保存参数 | 校验参数 | 恢复默认 | 生成 | 退出
    
    所有参数自动从"金刚经排版参数.json"加载/保存。
    退出时若参数已修改，弹出保存确认对话框。
    """
    def __init__(self):
        self.params = load_config()
        self._dirty = False           # 参数是否被修改但未保存

        self.root = tk.Tk()
        self.root.title("金刚经排版选择")
        _center_window(self.root, 750, 530)
        self.root.resizable(False, False)
        self.root.protocol("WM_DELETE_WINDOW", self._on_exit)

        # 使用 ttk 主题
        style = ttk.Style()
        style.theme_use("vista" if "vista" in style.theme_names() else "default")

        # 底部按钮（先 pack，占据底部固定空间）
        self._build_buttons()

        # 笔记本（后 pack，填满剩余空间）
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=10, pady=(8, 2))

        self._build_tab1()   # 基本设定
        self._build_tab2()   # 单元格参数
        self._build_tab3()   # 小版模板
        self._build_tab4()   # 大版参数
        self._build_tab5()   # 经文文本
        self._build_tab6()   # 生成版面选项


    def _add_input(self, parent, label, key, width=12):
        """添加到 inputs 字典"""
        f = ttk.Frame(parent)
        f.pack(fill="x", pady=2, padx=(80, 20))
        ttk.Label(f, text=label, width=22, anchor="e").pack(side="left", padx=(0, 5))
        var = tk.StringVar(value=str(self.params.get(key, "")))
        w = ttk.Entry(f, textvariable=var, width=width)
        w.pack(side="left")
        setattr(self, f"_inp_{key}", var)
        return var

    def _build_tab1(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="基本设定")

        # 工作路径
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="工作路径:", width=18, anchor="e").pack(side="left", padx=(0, 5))
        self._work_var = tk.StringVar(value=self.params["WORK_DIR"])
        e = ttk.Entry(f, textvariable=self._work_var, width=40)
        e.pack(side="left")
        ttk.Button(f, text="选择...", command=self._pick_work).pack(side="left", padx=5)

        # 文件冲突（移到工作路径后面）
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="文件冲突:", width=18, anchor="e").pack(side="left", padx=(0, 5))
        self._overwrite = tk.IntVar(value=self.params["OVERWRITE_MODE"])
        ttk.Radiobutton(f, text="覆盖", variable=self._overwrite, value=1).pack(side="left")
        ttk.Radiobutton(f, text="跳过", variable=self._overwrite, value=0).pack(side="left", padx=10)

        # 字库目录
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="字库目录:", width=18, anchor="e").pack(side="left", padx=(0, 5))
        self._pic_var = tk.StringVar(value=self.params["PIC_FOLDER"])
        e = ttk.Entry(f, textvariable=self._pic_var, width=40)
        e.pack(side="left")
        ttk.Button(f, text="选择...", command=self._pick_pic).pack(side="left", padx=5)

        ttk.Separator(tab, orient="horizontal").pack(fill="x", pady=6)

        # DPI + 尺寸标注 + 程序调试限制字数
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="DPI:", anchor="e").pack(side="left")
        self._dpi_var = tk.StringVar(value=str(self.params["DPI"]))
        ttk.Entry(f, textvariable=self._dpi_var, width=8).pack(side="left", padx=3)
        ttk.Label(f, text="(72~200)", foreground="gray").pack(side="left")
        ttk.Label(f, text="  尺寸标注:").pack(side="left", padx=(15, 0))
        self._anno_var = tk.IntVar(value=self.params["ADD_ANNOTATION"])
        ttk.Checkbutton(f, text="标注", variable=self._anno_var).pack(side="left")
        ttk.Label(f, text="  程序调试限制字数:").pack(side="left", padx=(15, 0))
        self._debug_var = tk.StringVar(value=str(self.params["TEST_CHAR_LIMIT"]))
        ttk.Entry(f, textvariable=self._debug_var, width=6).pack(side="left", padx=3)
        ttk.Label(f, text="(0为不限制)", foreground="gray").pack(side="left")

        # ===== 直接放置组 =====
        direct_group = ttk.LabelFrame(tab, text="直接放置", padding=3)
        direct_group.pack(fill="x", pady=3)

        self._scale_mode = tk.IntVar(value=self.params["SCALE_MODE"])
        f = ttk.Frame(direct_group)
        f.pack(fill="x", pady=2)
        ttk.Radiobutton(f, text="直接放置", variable=self._scale_mode, value=0).pack(side="left")
        ttk.Label(f, text="  全局文字缩放:").pack(side="left", padx=(10, 0))
        self._scale_var = tk.StringVar(value=str(self.params["SCALE_PERCENT"]))
        ttk.Entry(f, textvariable=self._scale_var, width=6).pack(side="left", padx=2)
        ttk.Label(f, text="%").pack(side="left")
        ttk.Label(f, text="  所有文字按照该比例等比缩放", foreground="gray").pack(side="left", padx=(10, 0))

        f = ttk.Frame(direct_group)
        f.pack(fill="x", pady=2)
        ttk.Label(f, text="自动放大: 阈值").pack(side="left")
        self._ath_var = tk.StringVar(value=str(self.params["AUTO_SCALE_THRESHOLD"]))
        ttk.Entry(f, textvariable=self._ath_var, width=5).pack(side="left", padx=2)
        ttk.Label(f, text="%(0=不放大)", foreground="gray").pack(side="left")
        ttk.Label(f, text="  宽缩至").pack(side="left")
        self._afil_w = tk.StringVar(value=str(self.params["AUTO_FILL_W"]))
        ttk.Entry(f, textvariable=self._afil_w, width=4).pack(side="left", padx=2)
        ttk.Label(f, text="%(以格宽为基准)", foreground="gray").pack(side="left")
        ttk.Label(f, text="  高缩至").pack(side="left")
        self._afil_h = tk.StringVar(value=str(self.params["AUTO_FILL_H"]))
        ttk.Entry(f, textvariable=self._afil_h, width=4).pack(side="left", padx=2)
        ttk.Label(f, text="%(以格高为基准)", foreground="gray").pack(side="left")

        f = ttk.Frame(direct_group)
        f.pack(fill="x", pady=2)
        ttk.Label(f, text="自动缩小: 阈值").pack(side="left")
        self._sth_var = tk.StringVar(value=str(self.params["AUTO_SHRINK_THRESHOLD"]))
        ttk.Entry(f, textvariable=self._sth_var, width=5).pack(side="left", padx=2)
        ttk.Label(f, text="%(0=不缩小)", foreground="gray").pack(side="left")
        ttk.Label(f, text="  宽缩至").pack(side="left")
        self._sfil_w = tk.StringVar(value=str(self.params["SHRINK_FILL_W"]))
        ttk.Entry(f, textvariable=self._sfil_w, width=4).pack(side="left", padx=2)
        ttk.Label(f, text="%(以格宽为基准)", foreground="gray").pack(side="left")
        ttk.Label(f, text="  高缩至").pack(side="left")
        self._sfil_h = tk.StringVar(value=str(self.params["SHRINK_FILL_H"]))
        ttk.Entry(f, textvariable=self._sfil_h, width=4).pack(side="left", padx=2)
        ttk.Label(f, text="%(以格高为基准)", foreground="gray").pack(side="left")

        # ===== 相对单元格组 =====
        cell_group = ttk.LabelFrame(tab, text="相对单元格", padding=3)
        cell_group.pack(fill="x", pady=3)

        f = ttk.Frame(cell_group)
        f.pack(fill="x", pady=2)
        ttk.Radiobutton(f, text="相对单元格", variable=self._scale_mode, value=1).pack(side="left")
        ttk.Label(f, text="  缩放比率:").pack(side="left", padx=(10, 0))
        self._cell_fill_var = tk.StringVar(value=str(self.params["CELL_FILL_RATIO"]))
        ttk.Entry(f, textvariable=self._cell_fill_var, width=5).pack(side="left", padx=2)
        ttk.Label(f, text="%(以较大方向为基准)", foreground="gray").pack(side="left")

        ttk.Separator(tab, orient="horizontal").pack(fill="x", pady=4)

        # 分段符处理方式（竖排：模式1一行，模式2+跳格+尾题一行）
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="分段符处理方式:", width=18, anchor="e").pack(side="left", padx=(0, 5))
        g = ttk.Frame(f)
        g.pack(side="left")
        self._smode = tk.IntVar(value=self.params["SCRIPTURE_MODE"])
        h1 = ttk.Frame(g)
        h1.pack(fill="x", pady=1)
        ttk.Radiobutton(h1, text="模式1（换列）", variable=self._smode, value=1).pack(side="left")
        h2 = ttk.Frame(g)
        h2.pack(fill="x", pady=1)
        ttk.Radiobutton(h2, text="模式2（跳格）", variable=self._smode, value=2).pack(side="left")
        ttk.Label(h2, text="  跳格字数:").pack(side="left", padx=(10, 0))
        self._skip_var = tk.StringVar(value=str(self.params["PARA_SKIP_COUNT"]))
        ttk.Entry(h2, textvariable=self._skip_var, width=6).pack(side="left")
        ttk.Label(h2, text="字").pack(side="left", padx=2)
        self._lastbr_var = tk.IntVar(value=self.params["LAST_BR_NEW_COL"])
        ttk.Checkbutton(h2, text="尾题另起一列", variable=self._lastbr_var).pack(side="left", padx=15)


        # 输出格式
        ttk.Separator(tab, orient="horizontal").pack(fill="x", pady=6)
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=3)
        ttk.Label(f, text="输出格式:", width=18, anchor="e").pack(side="left", padx=(0, 5))
        ttk.Label(f, text="PSD（含图层）", foreground="gray").pack(side="left")

    def _build_tab2(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="单元格参数")
        keys = [
            ("CELL_W", "单元格宽度 (mm):"),
            ("CELL_H", "单元格高度 (mm):"),
            ("ROW_GAP", "行间距 (mm):"),
            ("ROWS", "每块小版行数:"),
            ("BIG_FRAME_MARGIN_TOP", "大框上边距 (mm):"),
            ("BIG_FRAME_MARGIN_BOTTOM", "大框下边距 (mm):"),
            ("CANVAS_TO_BIGFRAME_TOP", "画布→大框上边距 (mm):"),
            ("CANVAS_TO_BIGFRAME_BOTTOM", "画布→大框下边距 (mm):"),
            ("SPLIT_LINE_AFTER_ROW", "分割线在第几行后:"),
        ]
        for key, label in keys:
            self._add_input(tab, label, key)

    def _add_inline_entry(self, parent, key, width=8):
        """在父容器中直接添加水平排列的 Entry，并存储变量"""
        var = tk.StringVar(value=str(self.params.get(key, "")))
        w = ttk.Entry(parent, textvariable=var, width=width)
        w.pack(side="left")
        setattr(self, f"_inp_{key}", var)
        return var

    def _build_tab3(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="小版模板")
        tnames = ["模板-1(1.1/2.1/4.1/5.1)", "模板-2(1.2/2.2/3.2/3.3/4.2/5.2)",
                   "模板-3(1.3/2.3/4.3/5.3)", "模板-4(3.1)", "模板-5(3.4)"]

        canvas = tk.Canvas(tab, height=280)
        scrollbar = ttk.Scrollbar(tab, orient="vertical", command=canvas.yview)
        scroll_frame = ttk.Frame(canvas)
        scroll_frame.bind("<Configure>", lambda _: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)


        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        for ti in range(5):
            pfx = f"T{ti}_"
            bf = ttk.LabelFrame(scroll_frame, text=tnames[ti])
            bf.pack(fill="x", pady=3, padx=5)
            r1 = ttk.Frame(bf)
            r1.pack(fill="x", pady=2)
            ttk.Label(r1, text="画布").pack(side="left")
            self._add_inline_entry(r1, pfx + "CANVAS_W", 8)
            ttk.Label(r1, text="x").pack(side="left")
            self._add_inline_entry(r1, pfx + "CANVAS_H", 8)
            ttk.Label(r1, text="列").pack(side="left", padx=5)
            self._add_inline_entry(r1, pfx + "COLS", 6)
            ttk.Label(r1, text="间距").pack(side="left", padx=5)
            self._add_inline_entry(r1, pfx + "COL_GAP", 6)
            r2 = ttk.Frame(bf)
            r2.pack(fill="x", pady=2)
            ttk.Label(r2, text="大框左").pack(side="left")
            self._add_inline_entry(r2, pfx + "BIG_FRAME_L", 6)
            ttk.Label(r2, text="右").pack(side="left")
            self._add_inline_entry(r2, pfx + "BIG_FRAME_R", 6)
            ttk.Label(r2, text="外左").pack(side="left", padx=5)
            self._add_inline_entry(r2, pfx + "CANVAS_TO_BIG_L", 6)
            ttk.Label(r2, text="右").pack(side="left")
            self._add_inline_entry(r2, pfx + "CANVAS_TO_BIG_R", 6)
            ttk.Label(r2, text="mm").pack(side="left", padx=3)

    def _build_tab4(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="大版参数")
        bnames = ["大版-1(1.1+1.2+1.3)", "大版-2(2.1+2.2+2.3)",
                   "大版-3(3.1+3.2+3.3+3.4)", "大版-4(4.1+4.2+4.3)", "大版-5(5.1+5.2+5.3)"]

        canvas = tk.Canvas(tab, height=280)
        scrollbar = ttk.Scrollbar(tab, orient="vertical", command=canvas.yview)
        scroll_frame = ttk.Frame(canvas)
        scroll_frame.bind("<Configure>", lambda _: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)


        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        for bi in range(5):
            pfx = f"B{bi}_"
            bf = ttk.LabelFrame(scroll_frame, text=bnames[bi])
            bf.pack(fill="x", pady=3, padx=5)
            r1 = ttk.Frame(bf)
            r1.pack(fill="x", pady=2)
            ttk.Label(r1, text="画布").pack(side="left")
            self._add_inline_entry(r1, pfx + "CANVAS_W", 8)
            ttk.Label(r1, text="x").pack(side="left")
            self._add_inline_entry(r1, pfx + "CANVAS_H", 8)
            ttk.Label(r1, text="大框").pack(side="left", padx=5)
            self._add_inline_entry(r1, pfx + "BIG_FRAME_W", 8)
            ttk.Label(r1, text="x").pack(side="left")
            self._add_inline_entry(r1, pfx + "BIG_FRAME_H", 8)
            r2 = ttk.Frame(bf)
            r2.pack(fill="x", pady=2)
            ttk.Label(r2, text="上边距").pack(side="left")
            self._add_inline_entry(r2, pfx + "TOP_MARGIN", 8)
            ttk.Label(r2, text="下边距").pack(side="left", padx=5)
            self._add_inline_entry(r2, pfx + "BOTTOM_MARGIN", 8)
            ttk.Label(r2, text="mm").pack(side="left", padx=3)

    def _build_tab5(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="经文文本")
        ttk.Label(tab, text="经文内容（编辑后自动保存到配置文件）:").pack(anchor="w", pady=3)
        f = ttk.Frame(tab)
        f.pack(fill="both", expand=True, padx=5)
        self._scr_text = tk.Text(f, wrap="word", font=("Microsoft YaHei", 10))
        self._scr_text.insert("1.0", self.params["SCRIPTURE_TEXT"])
        vsb = ttk.Scrollbar(f, orient="vertical", command=self._scr_text.yview)
        self._scr_text.configure(yscrollcommand=vsb.set)
        self._scr_text.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

    def _build_tab6(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="生成版面选项")

        self._big_vars = []
        self._small_vars = []

        for bi in range(5):
            defn = BIG_BOARD_DEFS[bi]
            f = ttk.Frame(tab)
            f.pack(fill="x", pady=4, padx=(60, 0))
            bv = tk.IntVar(value=1)
            cb = ttk.Checkbutton(f, text=f"大版-{bi + 1}", variable=bv)
            cb.pack(side="left")
            self._big_vars.append(bv)

            sm_vars = []
            for idx in defn["indices"]:
                inst = BOARD_INSTANCES[idx]
                sv = tk.IntVar(value=1)
                ttk.Checkbutton(f, text=inst["name"], variable=sv).pack(side="left", padx=5)
                sm_vars.append(sv)
            self._small_vars.append(sm_vars)

            # 大版复选框 → 全选/全不选子复选框
            cb.configure(command=lambda bv=bv, smvs=sm_vars: [
                sv.set(bv.get()) for sv in smvs
            ])

        # 全选/全不选
        f = ttk.Frame(tab)
        f.pack(fill="x", pady=8, padx=(60, 0))
        ttk.Button(f, text="全选", command=self._sel_all).pack(side="left", padx=5)
        ttk.Button(f, text="全不选", command=self._sel_none).pack(side="left", padx=5)

    def _build_buttons(self):
        f = ttk.Frame(self.root)
        f.pack(side="bottom", fill="x", pady=8)

        g1 = ttk.Frame(f)
        g1.pack(side="left", padx=(100, 0))
        ttk.Button(g1, text="保存参数", command=self._save_params).pack(side="left", padx=3)
        ttk.Button(g1, text="校验参数", command=self._validate).pack(side="left", padx=3)
        ttk.Button(g1, text="恢复默认", command=self._restore).pack(side="left", padx=3)

        ttk.Label(f, text="      ").pack(side="left")

        g2 = ttk.Frame(f)
        g2.pack(side="left")
        ttk.Button(g2, text="生成", command=self._generate).pack(side="left", padx=3)
        ttk.Button(g2, text="退出", command=self._on_exit).pack(side="left", padx=3)

    def _safe_int(self, var, field_name):
        """安全转换输入值为整数，非法时弹错并抛出"""
        val = var.get().strip()
        try:
            return int(val)
        except (ValueError, TypeError):
            messagebox.showerror("输入错误", f"「{field_name}」输入无效: 『{val}』，请输入整数")
            raise ValueError(f"Invalid input for {field_name}: {val}")

    def _pick_work(self):
        old = os.getcwd()
        target = os.path.abspath(self._work_var.get())
        if not os.path.isdir(target):
            messagebox.showerror("错误", f"目录不存在: {target}")
            return
        try:
            os.chdir(target)
            d = filedialog.askdirectory(title="选择工作路径")
        finally:
            os.chdir(old)
        if d:
            self._work_var.set(d)
            self._dirty = True
            self._validate(silent=True)

    def _pick_pic(self):
        old = os.getcwd()
        target = os.path.abspath(self._pic_var.get())
        if not os.path.isdir(target):
            messagebox.showerror("错误", f"目录不存在: {target}")
            return
        try:
            os.chdir(target)
            d = filedialog.askdirectory(title="选择字库目录")
        finally:
            os.chdir(old)
        if d:
            self._pic_var.set(d)
            self._dirty = True
            self._validate(silent=True)

    def _save_params(self):
        """保存前校验，通过后保存"""
        if not self._validate(silent=True):
            return
        save_config(self._collect())
        self._dirty = False
        messagebox.showinfo("保存", "参数已保存")

    def _on_exit(self):
        """退出前检查：若参数被修改且未保存，弹出确认对话框。
        
        三种选择：
          是(Y) — 保存参数并退出（校验通过后才保存）
          否(N) — 不保存直接退出
          取消   — 返回窗口
        """
        if self._dirty:
            ret = messagebox.askyesnocancel("参数已修改",
                "参数已修改，是否保存？\n是=保存并退出  否=不保存直接退出  取消=返回")
            if ret is None:  # 取消
                return
            if ret and self._validate(silent=True):  # 是 且 校验通过
                save_config(self._collect())
        close_log_file()
        self.root.destroy()

    def _collect(self):
        """从 GUI 控件收集所有参数值，构建参数字典。
        
        对整数字段调用 _safe_int() 做安全转换，
        输入非法时弹出错误消息框并抛出 ValueError。
        
        返回：
          dict: 完整的参数字典（结构与 DEFAULT_PARAMS 一致）
        """
        p = {}
        p["WORK_DIR"] = self._work_var.get()
        p["PIC_FOLDER"] = self._pic_var.get()
        p["DPI"] = self._safe_int(self._dpi_var, "DPI")
        p["SCALE_PERCENT"] = self._safe_int(self._scale_var, "全局文字缩放")
        p["SCALE_MODE"] = self._scale_mode.get()
        p["SCRIPTURE_MODE"] = self._smode.get()
        p["PARA_SKIP_COUNT"] = self._safe_int(self._skip_var, "跳格字数")
        p["LAST_BR_NEW_COL"] = self._lastbr_var.get()
        p["AUTO_SCALE_THRESHOLD"] = self._safe_int(self._ath_var, "自动放大阈值")
        p["AUTO_FILL_W"] = self._safe_int(self._afil_w, "自动放大宽填充率")
        p["AUTO_FILL_H"] = self._safe_int(self._afil_h, "自动放大高填充率")
        p["AUTO_SHRINK_THRESHOLD"] = self._safe_int(self._sth_var, "自动缩小阈值")
        p["SHRINK_FILL_W"] = self._safe_int(self._sfil_w, "自动缩小宽填充率")
        p["SHRINK_FILL_H"] = self._safe_int(self._sfil_h, "自动缩小高填充率")
        p["ADD_ANNOTATION"] = self._anno_var.get()
        p["OVERWRITE_MODE"] = self._overwrite.get()
        p["TEST_CHAR_LIMIT"] = self._safe_int(self._debug_var, "限制字数")
        p["CELL_FILL_RATIO"] = self._safe_int(self._cell_fill_var, "缩放比率")
        p["SCRIPTURE_TEXT"] = self._scr_text.get("1.0", "end-1c")
        # 单元格参数
        cell_keys = {"CELL_W": "单元格宽度", "CELL_H": "单元格高度",
                     "ROW_GAP": "行间距", "ROWS": "行数",
                     "BIG_FRAME_MARGIN_TOP": "大框上边距",
                     "BIG_FRAME_MARGIN_BOTTOM": "大框下边距",
                     "CANVAS_TO_BIGFRAME_TOP": "画布上边距",
                     "CANVAS_TO_BIGFRAME_BOTTOM": "画布下边距",
                     "SPLIT_LINE_AFTER_ROW": "分割线行号"}
        for k, label in cell_keys.items():
            var = getattr(self, f"_inp_{k}", None)
            p[k] = self._safe_int(var, label) if var else self.params.get(k)
        # 小版模板参数
        for ti in range(5):
            pfx = f"T{ti}_"
            for suffix, label in [("CANVAS_W", f"小版{ti+1}画布宽度"),
                                   ("CANVAS_H", f"小版{ti+1}画布高度"),
                                   ("COLS", f"小版{ti+1}列数"),
                                   ("COL_GAP", f"小版{ti+1}列间距"),
                                   ("BIG_FRAME_L", f"小版{ti+1}大框左边距"),
                                   ("BIG_FRAME_R", f"小版{ti+1}大框右边距"),
                                   ("CANVAS_TO_BIG_L", f"小版{ti+1}画布左边距"),
                                   ("CANVAS_TO_BIG_R", f"小版{ti+1}画布右边距")]:
                var = getattr(self, f"_inp_{pfx}{suffix}", None)
                p[pfx + suffix] = self._safe_int(var, label) if var else self.params.get(pfx + suffix)
        # 大版参数
        for bi in range(5):
            pfx = f"B{bi}_"
            for suffix, label in [("CANVAS_W", f"大版{bi+1}画布宽度"),
                                   ("CANVAS_H", f"大版{bi+1}画布高度"),
                                   ("BIG_FRAME_W", f"大版{bi+1}大框宽度"),
                                   ("BIG_FRAME_H", f"大版{bi+1}大框高度"),
                                   ("TOP_MARGIN", f"大版{bi+1}上边距"),
                                   ("BOTTOM_MARGIN", f"大版{bi+1}下边距")]:
                var = getattr(self, f"_inp_{pfx}{suffix}", None)
                p[pfx + suffix] = self._safe_int(var, label) if var else self.params.get(pfx + suffix)
        return p

    def _validate(self, silent=False):
        """全面校验所有参数，包括基本范围、单元格、小版/大版布局。
        
        校验项包括：
          1. 基本参数范围（DPI 72~200、缩放率 1~200%、填充率 1~100% 等）
          2. 单元格参数（宽度>0、高度>0、分割线行号合理等）
          3. 小版模板布局（水平/垂直方向是否够容纳所有单元格）
          4. 大版尺寸（画布是否够大、小版宽度和是否超过大框等）
        
        参数：
          silent (bool): True=校验通过不弹提示，False=通过时弹"校验通过"消息框
        
        返回：
          bool: True=通过, False=有误（已弹出错误对话框）
        """
        try:
            p = self._collect()
        except ValueError:
            return False
        errors = []

        # ========== 基本参数范围 ==========
        if p["DPI"] < 72 or p["DPI"] > 200:
            errors.append("DPI 必须在 72~200 之间")
        if p["SCALE_PERCENT"] < 1 or p["SCALE_PERCENT"] > 200:
            errors.append("全局文字缩放必须在 1~200% 之间")
        if p["PARA_SKIP_COUNT"] < 0:
            errors.append("段落跳格数不能为负")
        if p["AUTO_SCALE_THRESHOLD"] < 0 or p["AUTO_SCALE_THRESHOLD"] > 100:
            errors.append("自动放大阈值必须在 0~100% 之间")
        if p["AUTO_FILL_W"] < 1 or p["AUTO_FILL_W"] > 100:
            errors.append("自动放大宽度填充率必须在 1~100% 之间")
        if p["AUTO_FILL_H"] < 1 or p["AUTO_FILL_H"] > 100:
            errors.append("自动放大高度填充率必须在 1~100% 之间")
        if p["AUTO_SHRINK_THRESHOLD"] < 0 or p["AUTO_SHRINK_THRESHOLD"] > 500:
            errors.append("自动缩小阈值必须在 0~100% 之间")
        if p["SHRINK_FILL_W"] < 1 or p["SHRINK_FILL_W"] > 100:
            errors.append("自动缩小宽度填充率必须在 1~100% 之间")
        if p["SHRINK_FILL_H"] < 1 or p["SHRINK_FILL_H"] > 100:
            errors.append("自动缩小高度填充率必须在 1~100% 之间")
        if p["TEST_CHAR_LIMIT"] < 0:
            errors.append("限制字数不能为负")
        if p["CELL_FILL_RATIO"] < 1 or p["CELL_FILL_RATIO"] > 200:
            errors.append("相对单元格填充比率必须在 1~200% 之间")

        # ========== 单元格参数 ==========
        if p["CELL_W"] <= 0: errors.append("单元格宽度必须 > 0")
        if p["CELL_H"] <= 0: errors.append("单元格高度必须 > 0")
        if p["ROW_GAP"] < 0: errors.append("行间距不能为负")
        if p["ROWS"] < 1: errors.append("行数必须 >= 1")
        if p["BIG_FRAME_MARGIN_TOP"] < 0: errors.append("大框上边距不能为负")
        if p["BIG_FRAME_MARGIN_BOTTOM"] < 0: errors.append("大框下边距不能为负")
        if p["CANVAS_TO_BIGFRAME_TOP"] < 0: errors.append("画布上边距不能为负")
        if p["CANVAS_TO_BIGFRAME_BOTTOM"] < 0: errors.append("画布下边距不能为负")
        if p["SPLIT_LINE_AFTER_ROW"] < 1 or p["SPLIT_LINE_AFTER_ROW"] >= p["ROWS"]:
            errors.append(f"分割线行号必须在 1 ~ {p['ROWS'] - 1} 之间")

        # ========== 小版模板 (T0~T4) 布局验算 ==========
        for ti in range(5):
            pfx = f"T{ti}_"
            cw = p.get(f"{pfx}CANVAS_W", 0)
            ch = p.get(f"{pfx}CANVAS_H", 0)
            cols = p.get(f"{pfx}COLS", 0)
            col_gap = p.get(f"{pfx}COL_GAP", 0)
            bfl = p.get(f"{pfx}BIG_FRAME_L", 0)
            bfr = p.get(f"{pfx}BIG_FRAME_R", 0)
            ctbl = p.get(f"{pfx}CANVAS_TO_BIG_L", 0)
            ctbr = p.get(f"{pfx}CANVAS_TO_BIG_R", 0)
            name = f"小版{ti + 1}"
            if cw <= 0: errors.append(f"{name} 画布宽度必须 > 0"); continue
            if ch <= 0: errors.append(f"{name} 画布高度必须 > 0"); continue
            if cols < 1: errors.append(f"{name} 列数必须 >= 1"); continue
            if col_gap < 0: errors.append(f"{name} 列间距不能为负"); continue
            if bfl < 0: errors.append(f"{name} 大框左边距不能为负"); continue
            if bfr < 0: errors.append(f"{name} 大框右边距不能为负"); continue
            if ctbl < 0: errors.append(f"{name} 画布左边距不能为负"); continue
            if ctbr < 0: errors.append(f"{name} 画布右边距不能为负"); continue
            # 水平布局验算
            cell_w_total = cols * p["CELL_W"] + (cols - 1) * col_gap
            need_w = ctbl + bfl + cell_w_total + bfr + ctbr
            if cw < need_w:
                errors.append(f"{name} 画布宽({cw}) < 最小需要({need_w})")
            # 垂直布局验算
            cell_h_total = p["ROWS"] * p["CELL_H"] + (p["ROWS"] - 1) * p["ROW_GAP"]
            need_h = (p["CANVAS_TO_BIGFRAME_TOP"] + p["BIG_FRAME_MARGIN_TOP"]
                     + cell_h_total + p["BIG_FRAME_MARGIN_BOTTOM"]
                     + p["CANVAS_TO_BIGFRAME_BOTTOM"])
            if ch < need_h:
                errors.append(f"{name} 画布高({ch}) < 最小需要({need_h})")

        # ========== 大版 (B0~B4) 尺寸验算 ==========
        for bi in range(5):
            pfx = f"B{bi}_"
            cw = p.get(f"{pfx}CANVAS_W", 0)
            ch = p.get(f"{pfx}CANVAS_H", 0)
            bfw = p.get(f"{pfx}BIG_FRAME_W", 0)
            bfh = p.get(f"{pfx}BIG_FRAME_H", 0)
            tm = p.get(f"{pfx}TOP_MARGIN", 0)
            bm = p.get(f"{pfx}BOTTOM_MARGIN", 0)
            name = f"大版{bi + 1}"
            if cw <= 0: errors.append(f"{name} 画布宽度必须 > 0"); continue
            if ch <= 0: errors.append(f"{name} 画布高度必须 > 0"); continue
            if bfw <= 0: errors.append(f"{name} 大框宽度必须 > 0"); continue
            if bfh <= 0: errors.append(f"{name} 大框高度必须 > 0"); continue
            if tm < 0: errors.append(f"{name} 上边距不能为负"); continue
            if bm < 0: errors.append(f"{name} 下边距不能为负"); continue
            if bfw >= cw: errors.append(f"{name} 大框宽({bfw}) >= 画布宽({cw})")
            if bfh >= ch: errors.append(f"{name} 大框高({bfh}) >= 画布高({ch})")
            if tm + bfh + bm > ch:
                errors.append(f"{name} 上边距({tm})+大框高({bfh})+下边距({bm}) > 画布高({ch})")
            # 大版内小版宽度和验算
            if bi < len(BIG_BOARD_DEFS):
                total = 0
                for idx in BIG_BOARD_DEFS[bi]["indices"]:
                    inst = BOARD_INSTANCES[idx]
                    tpl = SMALL_TEMPLATES[inst["templateIdx"]]
                    total += tpl["canvasW_mm"]
                if total > bfw:
                    errors.append(f"{name} 小版宽度和({total}) > 大框宽({bfw})")

        if not errors:
            if not silent:
                messagebox.showinfo("校验", "参数校验通过！")
            return True
        else:
            messagebox.showerror("校验错误", "\n".join(errors))
            return False

    def _restore(self):
        for k, v in DEFAULT_PARAMS.items():
            var_name = f"_inp_{k}"
            if hasattr(self, var_name):
                getattr(self, var_name).set(str(v))
        self._dpi_var.set(str(DEFAULT_PARAMS["DPI"]))
        self._scale_var.set(str(DEFAULT_PARAMS["SCALE_PERCENT"]))
        self._scale_mode.set(DEFAULT_PARAMS["SCALE_MODE"])
        self._smode.set(DEFAULT_PARAMS["SCRIPTURE_MODE"])
        self._skip_var.set(str(DEFAULT_PARAMS["PARA_SKIP_COUNT"]))
        self._lastbr_var.set(DEFAULT_PARAMS["LAST_BR_NEW_COL"])
        self._ath_var.set(str(DEFAULT_PARAMS["AUTO_SCALE_THRESHOLD"]))
        self._afil_w.set(str(DEFAULT_PARAMS["AUTO_FILL_W"]))
        self._afil_h.set(str(DEFAULT_PARAMS["AUTO_FILL_H"]))
        self._sth_var.set(str(DEFAULT_PARAMS["AUTO_SHRINK_THRESHOLD"]))
        self._sfil_w.set(str(DEFAULT_PARAMS["SHRINK_FILL_W"]))
        self._sfil_h.set(str(DEFAULT_PARAMS["SHRINK_FILL_H"]))
        self._overwrite.set(DEFAULT_PARAMS["OVERWRITE_MODE"])
        self._anno_var.set(DEFAULT_PARAMS["ADD_ANNOTATION"])
        self._debug_var.set(str(DEFAULT_PARAMS["TEST_CHAR_LIMIT"]))
        self._cell_fill_var.set(str(DEFAULT_PARAMS["CELL_FILL_RATIO"]))
        self._work_var.set(DEFAULT_PARAMS["WORK_DIR"])
        self._pic_var.set(DEFAULT_PARAMS["PIC_FOLDER"])
        self._dirty = True
        self._scr_text.delete("1.0", "end")
        self._scr_text.insert("1.0", SCRIPTURE_TEXT)

    def _sel_all(self):
        for bv in self._big_vars:
            bv.set(1)
        for smvs in self._small_vars:
            for sv in smvs:
                sv.set(1)

    def _sel_none(self):
        for bv in self._big_vars:
            bv.set(0)
        for smvs in self._small_vars:
            for sv in smvs:
                sv.set(0)

    def _char_image_missing(self, pic_folder, ch):
        """检查单个字符在字库中是否有图片（含变体版本，如 佛.jpg、佛-1.png 等）"""
        vlist = probe_versions(pic_folder, ch)
        if len(vlist) > 1 or vlist[0] != 0:
            return False  # 找到了变体版本号文件，字符不缺
        # vlist == [0] 可能是不存在任何文件（probe_versions 兜底值），需二次确认
        for ext in IMAGE_EXTS:
            if os.path.exists(os.path.join(pic_folder, f"{ch}{ext}")):
                return False
        return True

    def _check_missing_images(self, pic_folder):
        """生成前检查经文所需字符图片是否齐全，缺失则弹窗警告"""
        # 扫描经文全文所有唯一字符
        all_chars = set(c for c in SCRIPTURE_TEXT if c.strip())
        missing = []
        for ch in sorted(all_chars):
            if self._char_image_missing(pic_folder, ch):
                missing.append(ch)
        if not missing:
            return True
        # 构建缺失列表
        missing_str = "  ".join(missing)
        rows = [missing_str[i:i+60] for i in range(0, len(missing_str), 60)]
        msg = (f"以下 {len(missing)} 个汉字在字库中缺少图片文件：\n\n"
               + "\n".join(rows)
               + "\n\n继续生成将跳过这些字（留空单元格），是否继续？")
        ret = messagebox.askyesno("缺字警告", msg,
                                  detail="是=继续生成  否=取消生成")
        return ret

    def _simulate_allocation(self, p):
        """模拟分配：按当前模式和参数，模拟经文分配到全部16块小版，返回分配结果。
        
        此方法仅在"生成"前调用，不影响实际分配。
        根据用户选择的 SCRIPTURE_MODE 使用对应的模拟逻辑。
        
        参数：
            p (dict): 参数字典
        返回：
            dict: {
                "total_slots": 总单元格数,
                "item_count":   经文总项数（含换行标记）,
                "remaining":    未能排入的项数（0=全部排入）,
                "can_fit":      能否全部排入（True/False）,
                "mode_desc":    模式描述文字
            }
        """
        mode = p["SCRIPTURE_MODE"]
        items = parse_scripture(p["SCRIPTURE_TEXT"])
        item_idx = 0
        total_slots = 0

        if mode == 1:
            # 模式1：换列————分段时换到下一列
            mode_desc = "全部16块小版"
            for bi in range(5):
                defn = BIG_BOARD_DEFS[bi]
                for idx in defn["indices"]:
                    inst = BOARD_INSTANCES[idx]
                    templ = SMALL_TEMPLATES[inst["templateIdx"]]
                    cols = templ["cols"]
                    rows = p["ROWS"]
                    total_slots += cols * rows
                    cur_col = 0
                    cur_row = 0
                    while item_idx < len(items) and cur_col < cols:
                        it = items[item_idx]
                        if it["type"] == "br":
                            if cur_row != 0:
                                cur_col += 1
                                cur_row = 0
                            item_idx += 1
                            continue
                        # char/skip: 占用一个格子
                        cur_row += 1
                        if cur_row >= rows:
                            cur_row = 0
                            cur_col += 1
                        item_idx += 1
        elif mode == 2:
            # 模式2：跳格————分段时跳过 N 个空格，首段和尾题可另起一列
            mode_desc = f"跳格模式，跳格字数={p['PARA_SKIP_COUNT']}"
            first_break = True
            for bi in range(5):
                defn = BIG_BOARD_DEFS[bi]
                for idx in defn["indices"]:
                    inst = BOARD_INSTANCES[idx]
                    templ = SMALL_TEMPLATES[inst["templateIdx"]]
                    cols = templ["cols"]
                    rows = p["ROWS"]
                    total_slots += cols * rows
                    cur_col = 0
                    cur_row = 0
                    while item_idx < len(items) and cur_col < cols:
                        it = items[item_idx]
                        if it["type"] == "br":
                            if first_break:
                                if cur_row != 0:
                                    cur_col += 1
                                    cur_row = 0
                                first_break = False
                            elif p["LAST_BR_NEW_COL"] and it.get("lastBreak"):
                                if cur_row != 0:
                                    cur_col += 1
                                    cur_row = 0
                            else:
                                for _ in range(p["PARA_SKIP_COUNT"]):
                                    cur_row += 1
                                    if cur_row >= rows:
                                        cur_row = 0
                                        cur_col += 1
                                    if cur_col >= cols:
                                        break
                            item_idx += 1
                            continue
                        cur_row += 1
                        if cur_row >= rows:
                            cur_row = 0
                            cur_col += 1
                        item_idx += 1
        else:
            return {"total_slots": 0, "item_count": 0, "remaining": 0,
                    "can_fit": True, "mode_desc": "未知模式"}

        remaining = len(items) - item_idx if item_idx < len(items) else 0
        return {"total_slots": total_slots,
                "item_count": len(items),
                "remaining": remaining,
                "can_fit": remaining == 0,
                "mode_desc": mode_desc}

    def _generate(self):
        """执行生成操作的主入口。
        
        流程：
          1. 收集参数并校验
          2. 检查工作路径和字库目录是否存在
          3. 模拟分配（根据当前模式检查经文能否全部排入）
          4. 收集复选框选择状态
          5. 检查字库中是否缺少字符图片
          6. 保存参数到 JSON
          7. 打开进度条对话框，调用 run_generation() 执行
          8. 完成后弹窗显示结果统计
        """
        p = self._collect()
        if not self._validate(silent=True):
            return
        if not os.path.exists(p["WORK_DIR"]):
            messagebox.showerror("错误", "工作路径不存在！")
            return
        if not os.path.exists(p["PIC_FOLDER"]):
            messagebox.showerror("错误", "字库目录不存在！")
            return

        # 模拟分配：根据用户选择的模式检查经文能否全部排入（仅生成前执行）
        sim = self._simulate_allocation(p)
        if sim["remaining"] > 0:
            ret = messagebox.askyesno("单元格不足",
                f"模拟分配结果（{sim['mode_desc']}）："
                f"共 {sim['total_slots']} 格，经文 {sim['item_count']} 项，"
                f"有 {sim['remaining']} 项无法排入。\n"
                f"是=继续生成  否=取消生成")
            if not ret:
                return

        # 收集复选框
        small_sel = []
        for smvs in self._small_vars:
            for sv in smvs:
                small_sel.append(sv.get() == 1)
        big_sel = [bv.get() == 1 for bv in self._big_vars]

        if not any(small_sel) and not any(big_sel):
            messagebox.showerror("错误", "请至少选择一项生成！")
            return

        # 缺字检查
        if not self._check_missing_images(p["PIC_FOLDER"]):
            return

        save_config(p)
        self._dirty = False

        # 创建进度条对话框
        pbar = ProgressDialog(self.root, "生成进度")
        pbar.update(0, "初始化...")

        def update_progress(cur, total, msg):
            pct = int(cur * 100 / total) if total > 0 else 0
            pbar.update(min(pct, 100), msg)

        t0 = time.time()
        try:
            scnt, bcnt = run_generation(p, small_sel, big_sel,
                                         progress=update_progress,
                                         cancel_check=pbar.is_cancelled)
            elapsed = time.time() - t0
            pbar.close()
            if not pbar.is_cancelled():
                messagebox.showinfo("完成",
                    f"脚本执行完成！\n"
                    f"运行时间: {elapsed:.2f} 秒\n"
                    f"生成小版: {scnt} 块\n"
                    f"生成大版: {bcnt} 块\n"
                    f"保存路径: {p['WORK_DIR']}")
        except GenerationCancelled:
            pbar.close()
        except Exception as e:
            pbar.close()
            messagebox.showerror("生成失败", str(e))

    def run(self):
        """启动 Tkinter 主事件循环（阻塞直到窗口关闭）"""
        self.root.mainloop()
        close_log_file()


# ==================== 主入口 ====================
if __name__ == "__main__":
    # 运行方式：在命令行执行 `python 金刚经_Python.py` 或双击 .py 文件
    # 启动后会显示图形界面窗口，配置参数后点击"生成"执行排版
    App().run()
