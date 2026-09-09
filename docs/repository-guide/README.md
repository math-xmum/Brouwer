# Brouwer / Gametheory 仓库导览

这是一份面向新贡献者的快速索引。仓库使用 Lean 4 和 mathlib，目标是形式化从 Scarf 组合引理、Brouwer 不动点定理到有限博弈混合 Nash 均衡存在性的证明。

## 从这里开始

- [scarf-primitive.md](scarf-primitive.md)：ScarfPath / Primitive 的接口入口、可编译用法与迁移说明。
- [structure.md](structure.md)：顶层目录、Lean 模块、实际导入关系和核心定理。
- [development.md](development.md)：环境准备、构建、单文件检查、CI 检查和常见维护命令。
- 仓库根目录的 [`README.md`](../../README.md)：数学证明路线、主要定义和定理的项目级说明。

## 30 秒概览

- 包名和 Lean 库名：`Gametheory`（见 `lakefile.lean`）。
- 默认入口：根目录的 `GameTheory.lean`。
- 源码位置：`Gametheory/*.lean`。
- 主要最终定理：`Gametheory/Nash.lean` 中的 `ExistsNashEq`。
- 固定工具链：Lean `4.33.0`（见 `lean-toolchain`）。
- 直接依赖：mathlib `v4.33.0`；清单记录的提交为 `db584cd6d46c92f209a44c0f1c829460d327499d`。
- 验证方式：当前仓库没有独立的单元测试目录或 Lake 测试目标；编译整个 Lean 库就是主要检查。

## 快速开始

先安装 `elan`。在仓库根目录执行：

```sh
lake build
```

`lean-toolchain` 会让 `elan` 选择项目要求的 Lean 版本；`lake-manifest.json` 固定依赖版本。首次构建需要取得依赖，因此耗时和网络要求会高于后续构建。

构建成功后，可以只检查某个正在修改的模块：

```sh
lake env lean Gametheory/Nash.lean
```

提交前仍应重新运行完整构建：

```sh
lake build
git status --short
```

`git status --short` 不是测试，但可帮助发现意外生成或修改的文件。不要为得到“干净”输出而删除自己不认识的改动。

## 推荐阅读顺序

1. `Gametheory/Simplex.lean`：标准单纯形的辅助构造。
2. `Gametheory/Scarf.lean`：有色 room/door 组合框架与 `Scarf`。
3. `Gametheory/ScarfPath.lean`：固定颜色图 `G_i` 及路径/环结构。
4. `Gametheory/Primitive.lean`：primitive/almost-primitive 表述、替换轨迹和坐标实现。
5. `Gametheory/Brouwer.lean`：单个有限维标准单纯形上的 `Brouwer`。
6. `Gametheory/Brouwer_product.lean`：有限多个单纯形乘积上的 `Brouwer_Product`。
7. `Gametheory/Nash.lean`：有限博弈、混合策略、Nash 映射和 `ExistsNashEq`。
8. `Gametheory/AxiomAudit.lean`：对主要端点执行 `#print axioms`。

这是一条理解数学内容的阅读路线，不完全等于编译器的导入顺序。例如 `Primitive.lean` 实际导入 `Brouwer.lean` 和 `ScarfPath.lean`，而 Nash 的直接依赖链并不导入 `Primitive.lean`。准确关系见 [structure.md](structure.md)。

## 已确认与未确认

本导览依据以下仓库内容整理：`README.md`、`lakefile.lean`、`lean-toolchain`、`lake-manifest.json`、`GameTheory.lean`、全部 `Gametheory/*.lean` 导入和主要声明、`.github/workflows/lean.yml`，以及本地存在的 `paper/cpp2027/README.md`。

尚未在仓库中确认的事项：

- 没有找到贡献流程、代码风格或分支策略的专门文档。
- 没有找到独立的测试套件或覆盖率配置。
- 没有找到发布/打包流程。
- CI 的 `nanoda` 检查由 `leanprover/lean-action@v1` 配置；仓库没有记录与之完全等价的本地命令。

遇到这些事项时，应先与维护者确认，而不是从本导览推断政策。
