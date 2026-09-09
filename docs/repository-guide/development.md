# 开发、构建与验证

以下命令默认从仓库根目录执行，除非另有说明。

## 环境要求

仓库配置明确固定了：

- Lean `4.33.0`：`lean-toolchain` 为 `leanprover/lean4:v4.33.0`。
- mathlib `v4.33.0`：由 `lakefile.lean` 声明。
- mathlib 精确提交 `db584cd6d46c92f209a44c0f1c829460d327499d`：由 `lake-manifest.json` 记录。

推荐通过 `elan` 安装和选择 Lean。可先确认命令可用：

```sh
elan --version
lake --version
```

在仓库内运行 `lake` 时，`elan` 会根据 `lean-toolchain` 选择版本。首次取得 Lean 工具链或 Lake 依赖需要网络。

## 完整构建

```sh
lake build
```

这是仓库记录的标准验证命令，也是根 `README.md`、论文草稿说明和 GitHub Actions 配置共同指向的检查。默认目标覆盖 `GameTheory.lean` umbrella 模块和 `Gametheory` 子模块。

构建会在 `.lake/` 下生成或更新缓存与中间产物。不要把构建输出中的变化误当成手写源码，也不要在不了解工作区状态时清理 `.lake/`。

## 快速检查单个文件

修改一个 Lean 文件时，可先直接检查它：

```sh
lake env lean Gametheory/Nash.lean
```

将路径替换为当前文件即可。检查 umbrella 入口可用：

```sh
lake env lean GameTheory.lean
```

由于 Lean 的导入机制会检查该文件的依赖，这适合快速反馈；提交前仍应运行 `lake build`，以覆盖所有通过 glob 纳入库但未必处于该文件依赖链上的模块。

## “测试”在本仓库中的含义

当前仓库没有发现：

- `test/` 或 `tests/` 目录；
- `lakefile.lean` 中单独的测试可执行目标；
- 传统单元测试框架或覆盖率配置。

因此目前的验证层次是：

1. 单文件/umbrella 的 Lean elaboration：`lake env lean ...`。
2. 全库构建：`lake build`，也检查 `Gametheory/Examples/ScarfPrimitive.lean` 的调用示例。
3. 公理审计：构建 `GameTheory.lean` 时导入 `Gametheory/AxiomAudit.lean`，其中对主要端点执行 `#print axioms`。
4. CI 附加检查：`.github/workflows/lean.yml` 使用 `leanprover/lean-action@v1`，配置 `build: true`、`nanoda: true`、`nanoda-allow-sorry: false`。

仓库没有写明与 CI `nanoda` 步骤完全等价的本地命令，因此这里不臆造命令。如果该 CI 文件尚未提交到你的分支，远端也不会运行它；以实际分支内容为准。

作为轻量静态检查，可以搜索未完成证明标记：

```sh
rg -n '\b(sorry|admit|axiom)\b' --glob '*.lean' .
```

这只能作为辅助，不能代替 Lean 构建或 `nanoda`。导览整理时，该搜索在当前 `.lean` 源码中没有命中。

## 常见开发命令

```sh
# 查看未提交变化；先做这一步再判断哪些文件属于自己
git status --short

# 查看项目声明的 Lean 工具链
sed -n '1p' lean-toolchain

# 查看各模块的直接导入
rg -n '^import ' --glob '*.lean' .

# 查找顶层声明
rg -n '^(theorem|lemma|def|structure|abbrev) ' Gametheory

# 完整构建
lake build
```

请保留工作区中已有的改动。尤其不要为了排除缓存问题直接执行会丢失修改的 Git 命令，也不要在不知道归属时删除 `.lake/`、`paper/`、`output/` 或 `tmp/`。

## 修改后的建议检查顺序

1. 用 `git status --short` 确认开始时已经存在的改动。
2. 编辑目标模块，并运行 `lake env lean path/to/module.lean`。
3. 若修改了定义或导入，检查所有下游模块；最可靠的方式是 `lake build`。
4. 检查是否引入 `sorry`/`admit`，并查看 `AxiomAudit` 输出是否符合预期。
5. 再次查看 `git status --short` 和差异，确保没有把生成文件当作源码提交。

仓库没有提供格式化器、lint 命令或明确的风格指南。除非维护者另有约定，建议延续相邻 Lean 代码的命名、命名空间和证明布局。

## 依赖与可复现性

为复现当前依赖版本，应保留 `lake-manifest.json`，直接运行构建。根 `README.md` 明确提示：制作冻结的提交工件时不要运行 `lake update`，因为该命令可能改变锁定的依赖修订。

如果确实要升级 Lean 或 mathlib，这是一项独立维护工作，至少应同步检查：

- `lean-toolchain`；
- `lakefile.lean` 中的 mathlib tag；
- 重新解析后的 `lake-manifest.json`；
- 全部 Lean 模块的完整构建和公理审计输出。

当前仓库没有记录依赖升级政策，执行升级前应与维护者确认。

## 论文草稿（可选、非 Lean 构建的一部分）

当前本地工作区存在 `paper/cpp2027/`，其 README 给出的命令是：

```sh
cd paper/cpp2027
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

这需要单独安装 LaTeX/`latexmk`。该目录在整理导览时是未跟踪内容，`lake build` 不会构建它；没有该目录的新克隆应跳过本节。

## 已验证范围

整理本导览时已确认：

- `elan`、`lake` 在当前环境可用；`lake --version` 报告其使用 Lean `4.33.0`。
- `GameTheory.lean` 导入七个证明模块和 `AxiomAudit.lean`。
- 所有 `Gametheory/*.lean` 的直接 `import` 与 [structure.md](structure.md) 中的图一致。
- 当前 `.lean` 文件中未搜索到 `sorry`、`admit` 或 `axiom` 关键字。
- `lake env lean GameTheory.lean` 执行成功。
- `lake build` 执行成功，报告 `Build completed successfully (8715 jobs)`；新增的一项是显式构建 umbrella module `GameTheory.lean`。`AxiomAudit` 对列出的端点均输出了 `propext`、`Classical.choice` 和 `Quot.sound`。

这些结果来自 2026-08-17 的当前工作区，只证明该状态下的构建；后续源码或依赖变化后需要重新验证。
