# JSP-001022 中文数学证明阐释稿

这是分阶段修订的文章源文件。先读[第一阶段交接说明](../../docs/JSP001022_STAGE1_REVIEW.md)，再按需要进入章节或[源码阅读指南](../../docs/JSP001022_SOURCE_GUIDE.md)。

| 文件 | 内容 |
| --- | --- |
| [jsp001022_exposition.tex](jsp001022_exposition.tex) | 主文件及版式配置 |
| [01-introduction.tex](sections/01-introduction.tex) | 问题、主定理和本阶段范围 |
| [02-density.tex](sections/02-density.tex) | 有限 Abel 不等式、离散主项及密度转换 |
| [03-chain.tex](sections/03-chain.tex) | 环境链所需结论及集合内子链提取 |
| [04-conversions.tex](sections/04-conversions.tex) | 截断、枚举和主定理组合 |
| [05-formalization.tex](sections/05-formalization.tex) | Lean 对应、显式引用及核查边界 |
| [references.tex](sections/references.tex) | 文献与固定代码版本 |

文章目前完整展开密度转换和子链提取；随机链、矩估计和反向 Fatou 的详细证明等待下一阶段。数学推导与 Lean 已导出的接口范围在文中分别说明。

本次只交付源文件，未运行 LaTeX 编译，未生成新 PDF。以后编译时应以本目录为工作目录，使主文件的章节路径正确解析；这不是本轮已执行的检查。
