# Erdős #360 (JSP-000298) 剩余缺口攻关手册

- **适用对象**：接手本项目的任何模型或工程师（本手册假设读者从零开始，只给它这份文件 + 仓库）。
- **基线**：`Erdos298.lean` SHA-256 `ECDB823729038B7873CD51FAAF867FD078DABBE98F792EEAAA2B6CC84A1883C0`（2026-09-19，`GuardedAPCover` 接口修正 + 参数侧非空见证之后）。`lake build Erdos298` 2049 jobs，exit 0，0 `sorry`，316 条 `#print axioms` 全部为 `[propext, Classical.choice, Quot.sound]`。
- **目标**：把 Conlon–Fox–Pham (2021, arXiv:2104.14766) 的渐近定理 $c\,F(n) \le f(n) \le C\,F(n)$，$F(n) = \dfrac{n^{1/3}\,(n/\varphi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}$，在 Lean 4 中做到 **0 外部假设**（HANDOVER §4 的 Level 4）。
- **本文结构**：§0 操作规程 → §1 现状与依赖图 → §2 逐个缺口（G0–G6）：数学内容 / 现有 Lean 接口 / 陷阱 / 引理拆分 / Mathlib 资源 / 验收 / 工作量 → §3 推荐顺序 → §4 附录（命令、模板、可复用引理索引）。

---

## §0 操作规程（先读，违者返工）

### 0.1 环境

| 项 | 值 |
| :-- | :-- |
| 工具链 | `leanprover/lean4:v4.33.0`（见 `lean-toolchain`） |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d`（见 `lake-manifest.json`，**不要动这两个文件**） |
| 主文件 | `Erdos298.lean`（≈10.9k 行，**CRLF 换行**，UTF-8）；子模块 `Erdos298/{Basic,DeVos,Kneser,Lev}.lean` |
| 依赖图 | `Basic → DeVos → Kneser → Erdos298`，`Basic → Lev → Erdos298`。新模块只能放在 `Erdos298/` 下并被 `Erdos298.lean` 导入；**不能反向导入 `Erdos298`**（会成环） |

编译很慢（主文件全量 ≈ 5–6 分钟）。**迭代时不要每次全量编译**：

1. 在项目根建一个临时 `Test.lean`，首行 `import Erdos298`（可再加你需要的 Mathlib 模块），把新代码写在 `namespace Erdos298 … end Erdos298` 里。
2. `lake env lean Test.lean`：只检查这一个文件，≈40 秒。
3. 通过后再把代码块搬进 `Erdos298.lean`（放在 `end Erdos298` 之前），补 `#print axioms`，跑一次 `lake build Erdos298`。
4. 如果本机没有 `.lake/`：同一台机器上 `work/sixtimenight-awards/submissions/jsp-001018/.lake/packages` 与 `work/jsp1018-cloud-cache-check/submissions/jsp-001018/.lake/packages` 已经编好了**完全相同**的 Mathlib（同 rev、同 toolchain）。可以复制源码到临时目录，用 junction（`cmd /c mklink /J <tmp>\.lake\packages <那个 packages 目录>`）复用，几分钟内即可编译，不必下载缓存。注意 `awards` 仓库的 `.gitignore` **没有**忽略 `.lake`，不要在提交目录里生成它。

### 0.2 红线（沿用 HANDOVER §1.2）

1. **不 commit、不 push。** 只在工作区改文件。
2. 只允许 `[propext, Classical.choice, Quot.sound]`；**0 `sorry`、0 `admit`、0 自定义 `axiom`**。
3. 带 `_of_…` 的定理是**条件式归约**，编译通过 ≠ 证完。汇报必须逐条列出未消除的假设。

### 0.3 空真（vacuity）自检——每加一个假设都要做

本项目已经踩过一次坑：`h_ap_cover` 是假命题，9 条"主定理"空真了两周，`#print axioms` 查不出来（见 PROGRESS §2.6 的 WARNING）。规程：

- 每引入一个 `def Hyp : Prop` 或定理里的显式假设 `h : …`，先在 `Test.lean` 里尝试写 `example : ¬ Hyp := by …`，把最平凡的取值（`d = 0`、`T = univ`、`T = ∅`、`Q = 1`、单元素集、子群本身）代进去。5 分钟内能反驳的，接口就是错的。
- 再尝试写一个具体见证 `example : Hyp := …` 或 `Nonempty Struct`。做不出见证的接口不要往下游用。
- 一个已经暴露、尚未修复的例子见 §2 G2：`HasAPRoughCountBound` 在真正需要它的参数区域是假命题。

### 0.4 验收等级（HANDOVER §4）

| 级别 | 判据 |
| :-- | :-- |
| Level 1 条件式归约 | 退出码 0，标准公理，假设显式列出 |
| Level 2 工具层闭合 | 具体引理无条件证完 |
| Level 3 主链阶段闭合 | Lemma 5.6 或某一方向渐近界无外部假设 |
| Level 4 奖题闭合 | `erdos_problem_360_asymptotic_master` 对 `F = cfpScale` 的两个见证都被证明，全库 0 sorry |

题库（`problems/catalog-0201-0300.md` JSP-000298）目前 `Lean proof: No / Eligible: No`。只有 Level 4 才改变这一状态。

---

## §1 现状与依赖图

### 1.1 已无条件完成（不必重做）

- 上界：`minColors_le_two_mul_s`（$2\lceil n^{1/3}\rceil$）、`minColors_le_sieve` / `minColors_le_of_prime_subset`（Alon–Erdős 筛法界）、`selberg_remainder_bound`（有限 Selberg 筛）、`minColors_le_conlon_fox_pham`（CFP 四层染色**显式公式**界）。
- 下界骨架：`minColors_ge_two`、`minColors_ge_of_cfp_witness`、`CFPDiverseWitness → k+1 ≤ f(n)`（`chromatic_lower_bound_of_diverse_density`）。
- 加法组合：DeVos 归纳法 Kneser（`Erdos298/DeVos.lean`）、任意合数模迭代和集增长 `iterSum_card_ge_of_zero_mem_of_generates`、CFP Lemma 2.5/2.6/2.7/5.4/5.5/5.8/5.11、Lemma 5.6 Claim 1（`growthSteps_card_le_p16Budget_closed`）、饱和分支 `card_subsetSumsMod_ge_of_saturated`。
- P08 Branch A `hasIntAPCoverBranchA`；P09 等差数列整除计数工具（`card_filter_dvd_toFinset_le` 等）。
- Lev (2010) **Lemma 1 的两集合鸽笼版** `lev_pigeonhole_interval`（不是 CFP 要用的 ℓ 重求和定理，见 G4）。
- 接口非空：`finiteConditions_realizable`、`cfpArithParams_realizable`、`p17FiniteArithConditions_realizable`、`lemma_5_6_parameter_hypotheses_satisfiable`。
- 结构接口等价：`guardedAPCover_iff_trichotomy`；反例 `not_unguarded_ap_cover'`。

### 1.2 尚未完成——依赖图

```
                         ┌──────────────────────────────────────────────┐
                         │  G1  GuardedAPCover  (DF/BP 小增长结构定理)   │
                         └───────────────┬──────────────────────────────┘
                                         │
 ┌───────────────────────┐   ┌───────────▼──────────────┐   ┌────────────────────────┐
 │ G3 HasIntAPCoverBranchB│──▶│ Lemma 5.6 (m = n) 无条件 │◀──│ G2 筛法接口重做 + 证明  │
 └───────────────────────┘   │  cfp_lemma_5_6_m_eq_n_*  │   └───────────┬────────────┘
                             └───────────┬──────────────┘               │
                                         │                              │ 共用
                             ┌───────────▼──────────────┐   ┌───────────▼────────────┐
                             │ G4 Lev 桥：模 t 稠密 →   │   │ Mertens / Chebyshev     │
                             │ 整数长区间 → 击中 n/v    │   │ 分析引理包 (Mertens.lean)│
                             │ → CFPDiverseWitness      │   └───────────┬────────────┘
                             └───────────┬──────────────┘               │
                                         │                              │
                             ┌───────────▼──────────────┐   ┌───────────▼────────────┐
                             │ G5 下界渐近参数族         │   │ G6 上界渐近             │
                             │ HasChromaticLowerBound   │   │ HasChromaticUpperBound  │
                             │        cfpScale c        │   │        cfpScale C       │
                             └───────────┬──────────────┘   └───────────┬────────────┘
                                         └──────────────┬───────────────┘
                                                        ▼
                                  erdos_problem_360_asymptotic_master (cfpScale)  = Level 4
```

G0（文档/工程卫生）不在图上，但要先做。

---

## §2 逐个缺口

格式统一：**A 数学** / **B 现有 Lean 接口** / **C 陷阱与已知问题** / **D 建议拆分** / **E Mathlib 资源** / **F 验收** / **G 工作量与风险**。

---

### G0 文档与工程卫生（先做，半天）

**问题清单**

1. `PROGRESS.md` 第 67–74 行：表格公式丢了 `$`（`\le m(m+1)/2 \implies …` 前面缺 `$n`）；第 307–321 行有 `\r` 被吃掉的乱码（"oughCount"、"dmit"）。修成合法 Markdown。
2. 文档中所有 "0 warnings" 的说法都不准确：当前 `lake build` 有 **40 条** `linter.style.haveILetI` 警告（都在修正前的旧行）。要么把这 40 处 `haveI`/`letI` 改成 `have`/`let`（linter 给出的 Try this），要么在文档统一改成"40 条风格警告"。前者更好，半小时。
3. `README.md` §"Formalized Theorems" 与 `PROGRESS.md` §1 表格是手工维护的，很容易与代码漂移。建议写一个 20 行的 Python 脚本，从 `Erdos298.lean` 抽出所有 `theorem/lemma/def` 名并与文档比对，输出"文档里有代码里没有 / 代码里有文档里没有"。
4. `PR_DESCRIPTION.md` 是 LF、其余文件是 CRLF；统一成 CRLF（git 已经在警告）。

**验收**：`lake build` 0 warning；脚本比对无差异。

---

### G1 `GuardedAPCover`：小增长集的结构定理（最硬，建议放最后）

**A 数学**

设 $N \ge 1$，$T \subseteq \mathbb{Z}/N\mathbb{Z}$，$d \in \mathbb{N}$。记 $\delta(T,x) = |(T+x)\setminus T|$，$G_d(T) = \{x : \delta(T,x) \le d\}$（"小增长集"，代码 `smallGrowth T d`）。需要证明的是 **Deshouillers–Freiman (2003) / Balasubramanian–Pandey 型**结构定理在本项目常数下的形式：

> 若 $8d < |T| < \xi N$，$0 < \xi \le 1/20$，且
> (i) $G_d(T)$ 生成整个 $\mathbb{Z}/N\mathbb{Z}$（排除真子群分支），
> (ii) $|G_d(T)| > 20\,(2d)^{51/50}/|T|^{1/50}$（排除"小基数"分支），
> 则存在子群 $H \le \mathbb{Z}/N\mathbb{Z}$、$c, v \in \mathbb{Z}/N\mathbb{Z}$、$\ell \in \mathbb{N}$，使得
> $$G_d(T) \subseteq \{c + jv + h : j < \ell,\ h \in H\},\qquad \ell\,|H| \le 128\,d.$$

直观：$G_d(T)$ 满足 $G_d + G_d \subseteq G_{2d}$（`iterSum_smallGrowth_subset`），且 $|G_{2d}| \le |T|^2/(|T|-2d)$（`card_smallGrowth_le_div`），所以 $G_d$ 是一个"近似子群"；DF 定理说低密度下的近似子群就是短的陪集等差数列。

**必须先做的事**：打开 arXiv:2104.14766，找到 CFP 引用的那条结构定理（§2 或 §5.1 里以 Deshouillers–Freiman / Balasubramanian–Pandey 命名的引理），**逐字核对常数** 20、51/50、1/50、128、1/20 的来源。本项目里这些常数是前人从论文抄来的，从未在 Lean 里被"使用"（因为整条链是接口），所以任何抄写错误都不会被编译器发现。核对结果写进 PROGRESS。

**B 现有接口**

```lean
def GuardedTrichotomy : Prop := ∀ N [NeZero N] T d xi, 8*d < T.card → 0 < xi → xi ≤ 1/20 →
  (T.card : ℝ) < xi * N → SmallGrowthTrichotomy N T d
def GuardedAPCover : Prop := ∀ N [NeZero N] T d xi, (同上四个守卫) →
  AddSubgroup.closure (smallGrowth T d : Set (ZMod N)) = ⊤ →
  20 * (2*d)^(51/50) / T.card^(1/50) < (smallGrowth T d).card →
  ∃ R : CosetAP N, smallGrowth T d ⊆ R.toFinset ∧ R.ell * |R.H| ≤ 128 * d
theorem guardedAPCover_iff_trichotomy : GuardedAPCover ↔ GuardedTrichotomy
```

`SmallGrowthTrichotomy N T d` 是三分支析取（真子群 / 小基数 / 陪集 AP）。使用点只有一个：`unsaturated_step_growth_of_ap_cover`。相关已证工具：`smallGrowth_subset_subgroup`、`proper_subgroup_of_three_coset_absorption`、`closure_card_le_three_of_iterSum_four_le_three`、`mul_128_lt_of_density`（$128d < N$）。

**C 陷阱**

1. **不要再去掉守卫。** 无守卫版本是假的（`not_unguarded_ap_cover'`）；去掉 (i) 也是假的（取 $T = H$ 真子群，$|H| = 2000$，$d = 10$，$N > 40000$：$G_d(T) = H$，任何 $\ell|H'| \le 1280$ 的陪集 AP 盖不住 2000 个点）。
2. Branch 2 的阈值 $20(2d)^{51/50}/|T|^{1/50}$ 数值上约等于 $40d/|T|^{0.02}$，比 $128d$ 小；所以定理实质是"$|G_d| \gtrsim 40d$ 且生成整群 $\Rightarrow$ $G_d$ 在大小 $\le 128d$ 的陪集 AP 里"。先用几个小例子（区间、两段区间、子群 + 区间、随机集）在纸上或用 Python 枚举 $N \le 60$ 验证陈述本身为真，再动手。
3. `CosetAP.toFinset` 用的是 `Finset.biUnion`，重复元素会被合并；`R.ell * |R.H|` 只是上界。构造时不必让 AP "proper"。

**D 建议拆分**（自底向上，每一步都是独立可验收的引理）

1. `smallGrowth_add_subset`：$G_a + G_b \subseteq G_{a+b}$（`delta_add_le` 的直接推论，可能已有等价物 `iterSum_smallGrowth_subset`）。
2. `card_smallGrowth_two_mul_le`：$|G_{2d}| \le \frac{|T|^2}{|T| - 2d} \le \frac{8}{7}|T|$（用 `card_smallGrowth_le_div`，条件 $8d < |T|$）。
3. **倍增常数**：$|G_d + G_d| \le |G_{2d}| \le \tfrac{8}{7}|T|$。要把它变成关于 $G_d$ 自身的倍增 $|G_d+G_d| \le K|G_d|$，需要 $|G_d| \gtrsim |T|/K'$。而假设 (ii) 只给 $|G_d| \gtrsim 40 d$，与 $|T|$ 无关——**这里是与 DF 原定理对接的关键**：DF 的假设是关于 $A = G_d$ 的 $|A+A| \le (2+\epsilon)|A|$ 且 $|A|$ 相对 $N$ 小；CFP 用它的方式一定还夹了一个"$|T|$ 与 $|G_d|$ 同阶或 $G_d$ 密"的引理。**先在论文里把这一步找出来**，把它写成一条独立的 Lean 命题（叫 `smallGrowth_doubling_of_large`），单独证。
4. Mathlib 已有的通用工具：`Finset.ruzsa_covering_mul`（Ruzsa 覆盖：$|A B| \le K|B| \Rightarrow A \subseteq F\cdot(B/B)$，$|F|\le K$）、`IsApproximateSubgroup`、`small_pow_of_small_tripling`、`Finset.mul_inv_eq_inv_mul_of_doubling_lt_two`（`VerySmallDoubling.lean`：倍增 $<2$ 时 $A$ 几乎是子群陪集）、`ZMod.cauchy_davenport`（素数模）。这些能给"$G_d$ 被少数几个 $G_d - G_d$ 的平移盖住"，但**给不出一维等差数列**；从近似子群到 AP 需要 Freiman 型定理，Mathlib 没有。
5. 最终定理 `guardedAPCover_of_DF`：由 3、4 及一个自己形式化的 DF 型引理推出 `GuardedAPCover`，再经 `guardedAPCover_iff_trichotomy` 得 `GuardedTrichotomy`，喂给 `cfp_lemma_5_6_finite_core_of_arith_conditional`。

**替代思路（未验证，仅供探索）**：使用点的 $T$ 不是任意集合，而是子集和的中心化纤维（`unsaturated_step_medium_fiber_and_smallGrowth` 给出的 $T$），它自带 $T = \Sigma_N(\cdot)$ 型结构（对某些平移几乎封闭）。也许对这类 $T$ 有比 DF 简单得多的直接论证（例如 $T$ 本身就是 AP 的并）。如果走这条路，接口应改为只对"纤维型 $T$"断言，而不是对所有 $T$。

**E Mathlib 资源**：`Mathlib.Combinatorics.Additive.{RuzsaCovering, ApproximateSubgroup, SmallTripling, VerySmallDoubling, CauchyDavenport, PluenneckeRuzsa}`，本项目 `Erdos298/DeVos.lean`（`kneser_bound_all`, `aperiodic_sumset_bound`）。

**F 验收**：`theorem guardedAPCover_proved : GuardedAPCover`，0 sorry；随后 `cfp_lemma_5_6_finite_core_of_arith_conditional` 与 `*_of_ap_cover` 链的签名中删除该假设并重新编译。

**G 工作量与风险**：形式化 DF 型定理的规模 ≈ 已完成的 DeVos.lean（1538 行）的 3–5 倍，且在开始前必须先确认论文里到底用的是哪条定理、常数是否对得上。这是全部缺口中唯一"可能做不出来"的一项。**建议最后做**，其他缺口不依赖它（它们只需要 Lemma 5.6 的结论作为假设）。

---

### G2 筛法接口重做（`HasAPRoughCountBound` / `APCoverSieveBridge`）

**C 先说已知问题（这是一个必须修的接口缺陷）**

当前接口：
```lean
def HasAPRoughCountBound (fc) (p) : Prop :=
  0 ≤ C ∧ ∀ (P : IntAP) (Q R_card : ℕ), R_card ≤ P.k ^ 3 → P.b ≤ fc.t →
    (roughCount P Q : ℝ) ≤ P.k * C        -- C := 256 * log(log n) / log r
```
- 对**所有** $Q$ 量化，而 `roughCount_one : roughCount P 1 = P.k`。取 $Q = 1$、$P.k = 1$、$P.b = 1$、$R_{card} = 0$ 得 $1 \le C$。反过来 $C \ge 1$ 时由 `roughCount_le_card` 它平凡成立。所以 **`HasAPRoughCountBound fc p ↔ 1 ≤ C`**，与筛法无关。
- 在使用点（`unsaturated_step_growth_of_ap_cover` 的矛盾推导）同时有 $M \le |B| \le \ell|H| \le 128D$（`card_le_card_cosetAP_of_image_subset`）和 E3：$384\,D\,C < M$。两者相加迫使 $C < 1/3$。**因此只要筛法真的被需要，`HasAPRoughCountBound` 就是假命题；它能被证明的区域恰好是它没用的区域。** 当前的 `concreteP17Conditions` 见证正是后一种情况（$C \approx 17$，矛盾其实来自 $M > 384D \ge 128 D \ge |B|$，筛法根本没参与）。
- `hasIntAPCoverBranchA` 输出的 $Q$ 是 **1**（`refine ⟨1, fun a _ => Nat.coprime_one_right a, cov, trivial⟩`），因为 `HasIntAPCover` 要求 `∀ a ∈ B, Nat.Coprime a Q`，而 $B$ 的元素 $a = qu$（`inY_v`）只有 $q$ 部分与 $W n$ 互素，$u \mid n$ 可以含小素因子，所以对 $a$ 本身能保证的互素模数只有 1。
- 结论：**P08/P09 的解耦架构（`HasIntAPCover` + `HasAPRoughCountBound` + `h_cov_sieve_of_lifting_and_sieve`）需要重做接口**，而不是"补证明"。

**A 数学（应该证明什么）**

CFP 的实际论证（§5.1 Claim 2 末尾）：候选集 $B \subseteq Y_v$ 被 $\le 2\ell|H|$ 条整数等差数列覆盖；$Y_v$ 的元素形如 $a = q u$，$u \mid n$，$u^{16} \le y$，$q$ 与 $Wn$ 互素（$W = \prod_{p \le z} p$）。对每条 AP $P = \{a_0 + jb : j < k\}$ 和每个 $u$，集合 $\{j : u \mid a_0 + jb\}$ 是 $j$ 的一个同余类，于是 $\{(a_0+jb)/u\}$ 又是一条 AP（长度 $\approx k/u$，步长 $b/\gcd(b,u)$ 的倍数）；对它用 Selberg **上界**筛（筛去 $\le z$ 的素数）得
$$\#\{j<k : u \mid a_0+jb,\ \gcd((a_0+jb)/u,\, W) = 1\} \;\le\; C_1\,\frac{k}{u}\cdot\frac{b}{\varphi(b)}\cdot\frac{1}{\log z} + z^4 .$$
对 $u \mid n$ 求和（$\sum_{u\mid n} 1/u \le n/\varphi(n)$ 一类的估计，或直接 $\sum_{u \mid n, u \le y^{1/16}} 1/u$），再用 $b/\varphi(b) \le C_2 \log\log n$（因为 $b \le t \le n$），得到 $|B| \le \ell|H| \cdot C_3 \dfrac{\log\log n}{\log z}$，这就是 98304 与 256 的来源（$z$ 与 $r$ 的关系、$\log z = \tfrac{1}{16}\log r$ 之类要重新核算）。

**B 需要的新接口（建议）**

```lean
/-- Y_v 型粗数计数：AP 中形如 q·u（u ∣ n, u^16 ≤ y, q 与 Q₀ 互素）的元素个数。 -/
def roughCountY (P : IntAP) (n y Q₀ : ℕ) : ℕ :=
  (P.toFinset.filter (fun z => ∃ u, u ∣ n ∧ u ^ 16 ≤ y ∧ (u : ℤ) ∣ z ∧ Nat.Coprime (z.natAbs / u) Q₀)).card

/-- 单条 AP 的筛法界，模数固定为 Q₀ = primorial z（不再对 Q 全称量化）。 -/
def HasAPRoughCountBoundY (fc) (p) (z : ℕ) : Prop :=
  ∀ P : IntAP, P.b ≤ fc.t → r_lower ≤ P.k →        -- r_lower 由 E2/h_min_len 决定，见下
    (roughCountY P p.n p.y (primorial z) : ℝ) ≤ P.k * C_sieve(n, z)
```
并把 `HasIntAPCover` 的 `hB_rough : ∀ a ∈ B, Coprime a Q` 改成"$B \subseteq Y_v$ 的像"（这已经由 `p.hA_inY` 免费给出，Branch A 不用再造 $Q$），`card_le_sieve_bound_of_cover` 改为对 `roughCountY` 求和。**所有常数（256、98304、$k^3$、E2 的 16、E3）都要按新推导重算**，然后更新 `concreteP17Conditions`（见证必须仍能通过，这就是它存在的意义）。

**D 引理拆分**

1. `roughCountY_le_sum_over_u`：$\mathrm{roughCountY}(P) \le \sum_{u \mid n,\ u^{16} \le y} \#\{j<k : u \mid a_0+jb \wedge \gcd((a_0+jb)/u, Q_0)=1\}$。纯计数。
2. `subAP_of_dvd`：固定 $u$，$\{j<k : u \mid a_0 + jb\}$ 是空集或一条步长 $u/\gcd(u,b)$ 的 AP；对应的商 $\{(a_0+jb)/u\}$ 是一条 `IntAP`，长度 $\le k/(u/\gcd(u,b)) + 1$。已有 `linear_dvd_sub_ge_d`、`card_le_div_add_one_of_separated` 可复用。
3. **AP 上的 Selberg 上界筛**（核心）：把 `Mathlib.NumberTheory.SelbergSieve` 的 `BoundingSieve` 实例化到 support = 一条 AP 的值、`nu d = 1/d`（对 $\gcd(d,b)=1$）或 $0$（$\gcd(d,b) > 1$，此时 AP 模 $p$ 是常数），`rem d` 由 `card_filter_dvd_toFinset_le` 控制在 $\le 1$。本项目 §2–3 对区间 $[1,m]$ 已经做过一模一样的事（`erdosBoundingSieve`、`siftedSum_eq_card_remainder`、`selbergWeight_isUpperMoebius`、`mainSum_selbergWeight_eq`、`errSum_selbergWeight_le`、`selberg_remainder_bound`）——**照抄结构，把 `Finset.Ico 1 m` 换成 `P.toFinset`**。产出：$\mathrm{siftedSum} \le k/G + z^4$，$G = \sum_{d \le z,\ d \mid Q_0,\ \gcd(d,b)=1} \mathrm{selbergTerms}(d)$。
4. **$G$ 的下界**：$G \ge \sum_{d \le z,\ \mu^2(d)=1,\ \gcd(d,b)=1} \frac{1}{\varphi(d)} \ge \frac{\varphi(b)}{b}\cdot c\log z$。分两步：(a) 无 $\gcd$ 限制时 $\sum_{d\le z}\mu^2(d)/d \ge \frac{6}{\pi^2}\sum_{m \le z} 1/m \ge \frac{1}{2}\log z$——**纯初等**（每个 $m \le z$ 唯一写成 $d k^2$，$d$ 无平方因子，$\sum 1/k^2 \le 2$），配合 Mathlib `log_le_harmonic_floor`；(b) 去掉与 $b$ 不互素的 $d$ 至多损失因子 $\prod_{p \mid b}(1-1/p) = \varphi(b)/b$（乘性）。
5. `totient_ratio_le_loglog`：$m/\varphi(m) \le C \log\log m$（$m \ge 16$）。路线：$\omega(m) \le \log_2 m$；$\prod_{p \mid m}(1-1/p)^{-1} \le \prod_{p \le p_{\omega}}(1-1/p)^{-1} \le \exp\big(\sum_{p \le x} \tfrac{2}{p}\big)$；$\sum_{p \le x} 1/p \le \log\log x + C$ 由 Chebyshev 上界 `Chebyshev.theta_le_log4_mul_x`（$\theta(x) \le x\log 4$）+ Abel 求和 `sum_mul_eq_sub_sub_integral_mul`（`Mathlib.NumberTheory.AbelSummation`）得到。这一条与 G5/G6 共用，**放进新模块 `Erdos298/Mertens.lean`**。
6. 组装：`HasAPRoughCountBoundY` 的证明 = 3 + 4 + 5 + 误差项 $z^4$ 的吸收（需要 $k \ge z^5$ 量级，据此**重新确定** `h_min_len` 和 E2 应该要求的 $k$ 与 $r$ 的关系，不要沿用 $R_{card} \le k^3$ 而不核算）。

**E Mathlib 资源**：`Mathlib.NumberTheory.SelbergSieve`（`BoundingSieve`, `siftedSum_le_mainSum_errSum_of_upperMoebius`, `selbergTerms_*`, `upperMoebius_lambdaSquared`）、`Mathlib.NumberTheory.Chebyshev`（`theta_le_log4_mul_x`, `theta_ge'`, `psi_ge'`）、`Mathlib.NumberTheory.AbelSummation`、`Mathlib.NumberTheory.Harmonic.Bounds`（`harmonic_le_one_add_log`, `log_le_harmonic_floor`）、`Mathlib.NumberTheory.Primorial`（`primorial_le_four_pow`, `Nat.Prime.dvd_primorial_iff`, `squarefree_primorial`）、`Nat.totient` 相关（`Nat.totient_mul`, `Nat.totient_prime_pow`）。**这个版本的 Mathlib 里没有 Mertens 定理**（`grep -ri mertens Mathlib/NumberTheory` 为空），只能从 Chebyshev + Abel 求和自己推。

**F 验收**：(1) 新接口在 $C_{sieve} < 1/3$ 的参数下**有见证**（写一个 `example`）；(2) `theorem hasAPRoughCountBoundY_proved : ∀ fc p z, (条件) → HasAPRoughCountBoundY fc p z`，0 sorry；(3) 整条 `*_of_lifting_and_sieve` 链改接新接口后仍编译，`concreteP17Conditions` 按新常数更新后仍通过。

**G 工作量**：接口重做 2–3 天；Selberg AP 筛 ~600 行（有模板）；$G$ 下界 ~300 行；`Mertens.lean`（第 5 条）~800–1500 行，是主要成本。共 3–5 周。风险：常数核算出错导致 E3 与其它条件不相容——所以见证必须同步维护。

---

### G3 `HasIntAPCoverBranchB`：小子群、长等差数列分支的整数提升

**A 数学**

上下文：$g = \gcd(t, \gcd B)$，$N = t/g$，$B/g \pmod N \subseteq R = \{c + jv + h : j < \ell, h \in H\}$，且 $\ell|H| \le 128D$。Branch A（`hasIntAPCoverBranchA`，已证）处理 $|H|^3 \ge \ell|H|$：沿 $H$ 方向提升——$H$ 循环，元素是 $N/|H|$ 的倍数，陪集 $c + jv + H$ 是模 $N$ 步长 $N/|H|$、长 $|H|$ 的 AP，**不回绕**，整数提升步长 $t/|H|$，每个陪集取 2 个平移副本（$a/g \in [0,2N)$），共 $2\ell$ 条。Branch B 是 $|H|^3 < \ell|H|$，即 $|H|^2 < \ell$：$H$ 小、$\ell$ 大，沿 $H$ 提升不满足 `h_min_len : R_card ≤ k^3`（$k = |H|$）。应改为**沿 $j$ 方向提升**：固定 $h \in H$，$\{c + h + jv : j < \ell\}$。此时 $R_{card} = \ell|H| < \ell^{3/2} \le \ell^3$，`h_min_len` 自动满足。

**B 现有接口**：`HasIntAPCoverBranchB fc p`（定义见 `Erdos298.lean` 约 10020 行），输出 `IntAPCover (B.image (↑)) R_card fc.t p.n`，其字段：`h_cov`（覆盖）、`h_sum_len`（长度和 $\le 3R_{card}$）、`h_min_len`（$R_{card} \le k^3$）、`h_step_pos`、`h_step_le_t`（步长 $\le t$）、`h_t_le_n`。构造器 `intAPCover_of_family`（任意索引族）、`intAPCover_of_coset_family`（等长族）。可直接复用的引理：`branchA_AP_cover` 的证明结构、`card_le_card_cosetAP_of_image_subset`、`zmod_subgroup_val_dvd`、`zmod_subgroup_scaled_val_dvd`。

**C 陷阱：回绕（wrap-around）**

取 $v' \in (-N/2, N/2]$ 为 $v$ 的整数代表（允许负步长：递减 AP 改写成起点更低的递增 AP 即可，`IntAP.b` 必须 $> 0$）。

- **不回绕子情形** $\ell\,|v'| < N$：$\{c + h + jv\}$ 的代表元恰为整数 AP $\{\mathrm{rep}(c+h) + j v'\}$（或递减），提升步长 $g|v'| \le gN = t$ ✓，长度 $\ell$，每个 $h$ 取 2 个平移副本，共 $2|H|$ 条，长度和 $2|H|\ell \le 3R_{card}$ ✓。**这一子情形现在就能证**，照 `branchA_AP` 的写法做一个 `branchB_AP`。
- **回绕子情形** $\ell\,|v'| \ge N$：模 $N$ 的 AP 在 $[0,N)$ 里的代表元不再是一条整数 AP。用 Dirichlet 逼近可取 $m \le \ell$ 使 $\|mv/N\| \le 1/\ell$，把它拆成 $m$ 条步长 $w = mv'$（$|w| \le N/\ell$）、长 $\approx \ell/m$、不回绕的整数 AP；但这样 `h_min_len` 变成 $\ell|H| \le (\ell/m)^3$，$m$ 大时不成立；而 `h_sum_len` 的 $3R_{card}$ 预算也只允许 $\le 3$ 个副本。**这不是证明技巧问题，是接口是否忠实于论文的问题。** 处理办法（按优先级）：
  1. 回论文查 CFP 是如何从 $\mathbb{Z}/t\mathbb{Z}$ 里的陪集 AP 得到整数 AP 的（Lemma 5.10 附近）。很可能论文的结构定理输出本身就带"$\ell |v'| < N$"或"AP 是 $[0,N)$ 的一段"的形式，或者论文的筛法是直接在 $\mathbb{Z}/t\mathbb{Z}$ 的等差数列上做的（那样 G2 的筛法接口也要跟着改成模 $t$ 的版本）。
  2. 如果论文确实允许回绕，则把 `IntAPCover.h_min_len` 改成只对"长度和的大部分"成立的加权版本，并让 G2 的筛法对短 AP 用平凡界（$\mathrm{roughCount} \le k$）——需要重新核算常数。
  3. 无论哪种，先把不回绕子情形证完（它是 Branch B 的主体），回绕子情形单独作为 `HasIntAPCoverBranchB_wrap` 假设留着，把 `hasIntAPCover_of_branchA_and_branchB` 改成三分支。

**D 拆分**

1. `zmod_rep_signed`：$v \in \mathbb{Z}/N\mathbb{Z}$ 的带符号代表 $v' \in (-N/2, N/2]$，`(v' : ZMod N) = v`。
2. `branchB_AP (fc p B R h s)`：`a := g * rep(c + h) + s * t` 或递减改写，`b := g * |v'|`，`k := ℓ`。
3. `branchB_AP_k`, `branchB_AP_b_le`（$g|v'| \le t$，用 $|v'| \le N/2 \le N$）。
4. `branchB_AP_cover`（不回绕假设下）：仿 `branchA_AP_cover`，核心是 $a/g \equiv c + h + jv \pmod N$ 且 $a/g \in [0,2N)$ $\Rightarrow$ $a = g(\mathrm{rep}(c+h) + jv') + sN g$，$s \in \{0,1\}$（或递减情形的对应式）。
5. `hasIntAPCoverBranchB_of_no_wrap`：装配 `intAPCover_of_coset_family`（$q = 2|H|$，$h := \ell$）。
6. 回绕子情形按 C 处理。

**F 验收**：`theorem hasIntAPCoverBranchB_of_no_wrap : … → HasIntAPCoverBranchB fc p`，0 sorry；`hasIntAPCover_of_branchA_and_branchB` 改成三分支后编译；回绕子情形有明确的接口名和 PROGRESS 记录。

**G 工作量**：不回绕 1–2 周（有 Branch A 模板）；回绕子情形取决于论文核对结果，可能触发 G2 接口联动。

---

### G4 Lev 桥：从"模 $t$ 稠密"到"击中 $n/v$"

**A 数学**

Lemma 5.6 的结论是 $|\Sigma_t(A)| \ge \min(\xi, 32/\ell)\,t$（模 $t$ 的子集和覆盖 $\ge \xi t$ 个剩余类），CFP Theorem 5.1 要的是 $n/v \in \Sigma(Q)$（整数子集和击中目标）。论文的路径：

1. 用 Lemma 5.4 把 $A$ 分成 $\ell$ 个互不相交、仍然多样的块 $A_1, \dots, A_\ell$（**已有**：`exists_disjoint_diverse_partition_of_div`）。
2. 对每块用 Lemma 5.6 得 $|\Sigma_t(A_i)| \ge \xi t$。
3. 把模 $t$ 的稠密性提升为整数集：取 $S_i \subseteq \Sigma(A_i)$ 为每个剩余类一个代表，且代表落在 $[0, q]$（$q \approx 2Kt$，因为贪心过程只用了 $K$ 个元素——`greedySeq`、`card_greedySeq_E`、`greedySeq_S_subset` 已经给出 $S_K = \Sigma_t(E_K)$，$|E_K| = K$，所以 $\Sigma(E_K) \subseteq [0, K \cdot \max A] \subseteq [0, 2Kt]$ 且 $|\Sigma(E_K)| \ge |\Sigma_t(E_K)| \ge \xi t$）。
4. **Lev (2010) Theorem 1**（ℓ 重求和）：$S_1, \dots, S_\ell \subseteq$ 长 $q+1$ 的区间，$|S_i| \ge m$，都不含于公差 $>1$ 的 AP，$\ell \ge 2\lceil (q-1)/(m-2) \rceil$，则 $S_1 + \cdots + S_\ell$ 含长 $\ell(m-1)+1$ 的连续整数区间。取 $m = \xi t$，$q = 2Kt$，$\ell \approx 4K/\xi$，得区间长 $\ge \ell\xi t/2 \ge 2Kt \ge 2t$。
5. 区间长 $\ge 2t >$ 剩余元素大小（$A$ 的元素 $< 2y/v \le 2t$），用 **已有**的 `mem_subsetSums_of_lev_interval_extend` 把区间沿剩余元素一路延伸到 $n/v$（需要 $n/v \le \sum A$，由参数保证）。
6. 得到 `HasLevIntervalCoverage n v Q` 或直接 `n/v ∈ subsetSums Q`，喂给 `CFPDiverseWitness.ofLevCoveragePred` → `minColors_ge_of_cfp_diverse_witness`。

**B 现有接口与差距**

- `Erdos298/Lev.lean` 里的 `lev_pigeonhole_interval` 是**两个集合**、要求 $|S_1| + |S_2| \ge \max(L_1,L_2) + 2$（即密度 $> 1/2$）的鸽笼版本；`HasLevIntervalCoverage`（`Erdos298.lean` 约 6840 行）也是按两个集合 $V_1, V_2$ 定义的。Lemma 5.6 只给密度 $\xi \approx 1/128$，**两集合版本不可能从 Lemma 5.6 接上**；必须形式化 ℓ 重求和的 Lev 定理（或 Freiman 型弱化版：低密度但多重求和）。
- "不含于公差 $>1$ 的 AP" 这个假设要从多样性推出：$S_i \ni 0$，故等价于 $\gcd(S_i) = 1$；由 Lemma 5.8 `subsetSumsMod_eq_univ_of_divisor_counts`（$\forall e \mid d,\ |A\setminus e\mathbb{N}| \ge e-1 \Rightarrow \Sigma_d(A) = \mathbb{Z}/d$）对所有 $2 \le d \le q$ 得 $\Sigma(A_i)$ 不落在任何公差 $d \le q$ 的 AP 里；$d > q$ 的 AP 在 $[0,q]$ 里至多 1 个点，而 $|S_i| \ge 2$。这要求 $A_i$ 的多样性参数 $k \ge q$ 量级——**检查 `exists_disjoint_diverse_partition_of_div` 给出的 $k/(2h)$ 是否够**，不够就要在 G5 的参数里放大 $k_{div}$。
- Lemma 5.6 现在的结论是关于 $\Sigma_t(A)$ 的；步骤 3 需要"用 $K$ 个元素就达到密度"的**加强版**。看 `cfp_lemma_5_6_finite_core` 的证明：饱和分支（`card_subsetSumsMod_ge_of_saturated`）用 `subsetSumsMod_eq_of_compl_dvd` 把 $\Sigma_t(E)$ 换成了 $\Sigma_t(A)$——这一步在整数上不成立（$A \setminus E$ 的元素虽然被 $g$ 整除，但加进去会改变整数和）。需要把结论改写成关于 $\Sigma_t(E_K)$ 或 $\Sigma_t(E_K \cup \text{少量元素})$ 的形式，或者在步骤 3 允许 $q$ 取 $|A| \cdot 2t$（那样 $\ell$ 要更大，参数要重算）。

**D 拆分**

1. `Erdos298/Lev.lean`：形式化 Lev (2010) Theorem 1（ℓ 重）。论文只有 9 页，证明是对 $\ell$ 归纳 + 两集合引理（已有 `lev_pigeonhole_interval` 可作为归纳步骤的一半）。先按原文陈述写 `theorem lev_high_multiplicity`，**核对原文假设**（HANDOVER §3.2 缺口 2 的转述不保证准确）。
2. `subsetSums_representatives`：从 $|\Sigma_t(E)| \ge m$ 选出 $S \subseteq \Sigma(E) \cap [0, \sum E]$，$|S| \ge m$，两两模 $t$ 不同余（`Finset.image` + 选择函数，或直接对 `subsetSumsMod` 的每个元素取 `Classical.choose`）。
3. `subsetSums_gcd_eq_one_of_diverse`：由 Lemma 5.8 推出 $S$ 不含于公差 $>1$ 的 AP。
4. `interval_of_partition`：把 1–3 对 $\ell$ 块组装，得 $\mathrm{Icc}\ a\ b \subseteq \Sigma(\bigcup A_i)$，$b - a \ge 2t$。
5. `hasLevIntervalCoverage_of_density`（或改写 `HasLevIntervalCoverage` 为 ℓ 块版本）：接 `mem_subsetSums_of_lev_interval_extend` 到 $n/v$。
6. Lemma 5.6 的"$K$ 元素加强版"（见 B 第三点），命名 `cfp_lemma_5_6_finite_core_bounded_support`。

**E Mathlib 资源**：`Mathlib.Combinatorics.Additive.SubsetSum`（`Finset.subsetSum`、`Finset.card_succ_choose_two_lt_card_subsetSum_of_pos`——注意它和本项目的 `subsetSums` 是两个定义，需要一个桥接引理）、`Finset.gcd`、`Nat.ModEq`。

**F 验收**：`theorem cfpDiverseWitness_of_lemma_5_6 : (Lemma 5.6 的结论对每块成立) → … → CFPDiverseWitness n k`，0 sorry。此时下界主链除 G1/G2/G3 外全部打通。

**G 工作量**：Lev 定理 ~800 行；桥接 ~1000 行；Lemma 5.6 加强版视情况 200–800 行。3–4 周。纯组合，**不依赖 Mathlib 缺失的东西**，是 G1–G6 中确定性最高的一项。

---

### G5 下界渐近参数族：`HasChromaticLowerBound cfpScale c`

**A 数学**（CFP Theorem 1.2 的参数选择，需对照论文 §5 逐项核对）

给定大 $n$：
- $v$：$n$ 的一个因子，用来吸收 $n/\varphi(n)$ 因子（论文里 $v$ 取 $n$ 的"光滑部分"或使 $n/v$ 与小素数互素）；
- $z \approx (\log n)^{c}$，$W = \prod_{p \le z} p$，$W \le 4^z$（`primorial_le_four_pow`）；
- $y \approx n^{1/3}(\log n)^{?}(\log\log n)^{?}$，$t \in [y/v, 2y/v)$；
- $\ell \approx \log\log n$，$\xi$ 为绝对常数；
- $A = Y_v \cap$（合适的剩余类），要证 $|A| \ge K + M$，即 $[y, 2y)$ 里"$q$ 与 $Wn$ 互素"的数至少 $\gg y \cdot \prod_{p \le z}(1-1/p) \cdot \varphi(n)/n \gg y/(\log z \cdot \log\log n)$。

最终要给出 `CFPAsymptoticParams n cfpScale c`（结构体在 `Erdos298.lean` 约 6940 行：`k`, `h_scale : c * F n ≤ k + 1`, `witness : CFPDiverseWitness n k`），再用 `hasChromaticLowerBound_of_asymptotic_params`。

**B 现有接口**：`CFPArithParams`、`P17FiniteArithConditions`（E1–E3、`hA_inY`）、`concreteCFPArithParams`（**单点**见证，可作为"参数族"的模板：把 16411、8192 等换成 $n$ 的函数）、`inY_v`、`cfpTau`、`cfpScale`、`cfpScale_pos_of_hyp`。

**C 陷阱**

1. 所有 E1–E3、`h_small_fiber_bound`、`h_growth_budget`、`h_numeric`（`p16TotalBudget`）必须对**所有** $n \ge N_0$ 同时成立，而不是某个 $n$；每一条都要写成关于 $n$ 的不等式并用 Chebyshev/Mertens 引理证明。`p16TotalBudget` 含 `Nat.log2 t`，用 `Nat.le_log2` / `Nat.log2_lt`（`witness_log2` 是模板）。
2. `h_subgroup_le : ∀ B ⊆ A, M ≤ |B| → subgroupIndex t B ≤ gMax` 在一般 $t$（非素数）下不再免费：需要 $A$ 的元素在模 $t$ 的每个素因子下都"不全被整除"。多样性 `IsDiverse A k_div` + `isDiverse_gcd_eq_one` + `subgroupIndex_eq_one_of_isDiverse` 已经能给 `subgroupIndex = 1`，前提是 $M$ 大到任何大小 $\ge M$ 的子集都多样（`isDiverse_subset_of_card_diff_le`）。
3. 粗数计数的**下界**（$|A| \ge K + M$）不是 Selberg 上界筛能给的；用 Legendre 容斥：$\#\{y \le a < 2y : \gcd(a, W)=1\} = y\prod_{p\le z}(1-1/p) + O(2^{\pi(z)})$，$z$ 取 $\le \log n$ 使误差 $2^{\pi(z)} \le 2^z \le n^{o(1)}$。乘性容斥在 Mathlib 里没有现成定理，但 `Nat.roughNumbersUpTo`（`SumPrimeReciprocals.lean` 里有 `Nat.roughNumbersUpTo_card_le'`）可作起点；或者用 `ArithmeticFunction.moebius` 的 `sum_divisors` 恒等式手写。

**D 拆分**

1. `Erdos298/Mertens.lean`（与 G2/G6 共用）：(M1) $\sum_{p\le x} 1/p \le \log\log x + C_1$；(M2) $\sum_{p \le x} 1/p \ge \log\log x - C_2$；(M3) $\prod_{p\le x}(1-1/p) \asymp 1/\log x$（两个方向，由 M1/M2 + $\log(1-1/p) = -1/p + O(1/p^2)$）；(M4) $m/\varphi(m) \le C\log\log m$。全部从 `Chebyshev.theta_le_log4_mul_x`、`Chebyshev.theta_ge'` + `AbelSummation` 推。
2. `rough_count_lower`：Legendre 容斥下界。
3. `cfpParams (n) : CFPArithParams` 与 `cfpP17 (n) : P17FiniteArithConditions _`，字段全部是关于 $n$ 的引理（每条一个 `lemma cfp_E1 (n) (hn : N₀ ≤ n) : …`）。
4. `cfp_scale_bound`：$k + 1 \ge c\cdot \mathrm{cfpScale}\,n$，其中 $k$ 来自 `CFPDiverseWitness` 的 `h_card : k * M < S.card`（$k \approx |S|/M$）。
5. 组装 `hasChromaticLowerBound_cfpScale : HasChromaticLowerBound cfpScale c`。

**F 验收**：`theorem hasChromaticLowerBound_cfpScale : ∃ c > 0, HasChromaticLowerBound cfpScale c`，0 sorry（在 G1–G4 闭合后无外部假设；在此之前允许以 `GuardedAPCover` 等为显式假设，但必须在文档中标 Level 1）。

**G 工作量**：`Mertens.lean` 1–2k 行；参数族与不等式 2–3k 行。6–10 周。风险：论文参数与 Lean 里的常数（E1 的 51/50、E3 的 98304 等）对不上时需要回溯 G2。

---

### G6 上界渐近：`HasChromaticUpperBound cfpScale C`（建议最先做的"真"渐近结果）

**A 数学**（CFP Theorem 1.5/1.6 上界）

已有 `minColors_le_conlon_fox_pham n s1 P d s_rem : f(n) ≤ s_1 + |P| + 2|\mathrm{reducedResidues}\,d| + \lceil |R_{cfp}|/s_{rem} \rceil$。要证：存在 $C$ 与 $N_0$，对 $n \ge N_0$ 可选 $s_1, P, d, s_{rem}$ 使右边 $\le C\,\mathrm{cfpScale}(n)$。论文的选择（核对 §1.2.1 / §4）大致是：$d$ 为 $n$ 的一个因子（或 $n$ 的小素因子之积）以产生 $n/\varphi(n)$，$P = \{p \le s_1 : p \nmid n\}$，$s_1 \approx s_{rem} \approx n^{1/3}(n/\varphi(n))/((\log n)^{1/3}(\log\log n)^{2/3})$，然后 $|R_{cfp}| \le |\mathrm{sieveRemainder}| \lesssim \dfrac{n}{s_1 \cdot \log s_1}\cdot\dfrac{n}{\varphi(n)}$（Selberg 上界筛 + Mertens），使 $|R_{cfp}|/s_{rem} \lesssim s_1$。

**B 现有接口**

- `HasChromaticUpperBound F C : Prop := 0 < C ∧ ∃ N0, ∀ n (hn : 2 ≤ n), N0 ≤ n → (minColors n hn : ℝ) ≤ C * F n`（约 1739 行）。**整个文件里它只出现在假设位置，从未被证明**。
- `selberg_remainder_bound n s z : |sieveRemainder n s (sievePrimes n s)| ≤ ⌊(n-1)/(s+1)⌋ / sieveG n s z + z^4`，`sieveG_ge_one_add_sum_primes : sieveG ≥ 1 + \sum_{p \in P, p \le z} 1/(p-1)`，`cfp_remainder_subset_sieve_remainder`（$R_{cfp} \subseteq$ Alon–Erdős 的 $R$）。
- `reducedResidues_card_le d : |reducedResidues d| ≤ d`（要用 $\varphi(d)$ 的精确值时用 `Nat.totient` 的对应引理：`reducedResidues d` 就是 $\{1..d\}$ 中与 $d$ 互素者，`Nat.totient_eq_card_coprime`）。

**C 陷阱**

1. 只用现有 `sieveG_ge_one_add_sum_primes` 得到的是 $G \ge 1 + \sum_{p \le z, p \nmid n} \frac{1}{p-1}$，要把它变成 $\gg \log z \cdot \varphi(n)/n$（或至少 $\gg \log\log z$ 量级的东西）就需要 Mertens (M2) 和"去掉 $p \mid n$ 的素数损失至多 $\prod_{p\mid n}$…"——即 G2/G5 里的 `Mertens.lean`。**先做 `Mertens.lean`**，三处共用。
2. 想拿到 $(\log n)^{1/3}(\log\log n)^{2/3}$ 的完整节省，需要用 G2 第 4 条的技巧把 $G$ 的下界从 $\sum 1/(p-1)$（$\approx \log\log z$）提升到 $\sum_{d \le z} \mu^2(d)/\varphi(d)$（$\approx \log z$）——现有 `sieveG_ge_one_add_sum_primes` 只取了 $d$ 为素数的项，扔掉了绝大部分。**这一步是上界能否达到 CFP 阶的关键**，纯初等（见 G2 D4(a)）。
3. 简化路线（如果只想先拿到一个无条件的渐近上界）：先证 $f(n) \le C n^{1/3}$（用 `minColors_le_two_mul_s` 加 $s = \lceil n^{1/3} \rceil$，几十行），再逐步加强。但 Level 4 要的是 CFP 阶，别停在这里。

**D 拆分**

1. `Mertens.lean`（同 G5 D1）。
2. `sieveG_ge_log`：$\mathrm{sieveG}\ n\ s\ z \ge c\cdot\frac{\varphi(n)}{n}\cdot\log z$（G2 D4 的技巧 + `selbergTerms` 乘性 `selbergTerms_isMultiplicative`）。
3. `cfp_upper_params (n)`：显式 $s_1, P, d, s_{rem}, z$ 及其正性/大小条件。
4. `cfpRemainder_card_le`：$|R_{cfp}| \le C' \dfrac{n}{s_1 \log z}\cdot\dfrac{n}{\varphi(n)}$（组合 `cfp_remainder_subset_sieve_remainder`、`selberg_remainder_bound`、2）。
5. `reducedResidues_card_eq_totient`、$2\varphi(d) \le 2d$ 与 $d$ 的选择。
6. 实数不等式收尾：把四项之和压到 $C\cdot\mathrm{cfpScale}(n)$；用 `Real.rpow` 的单调性引理与 `cfpScale` 的展开。
7. `hasChromaticUpperBound_cfpScale : ∃ C, HasChromaticUpperBound cfpScale C`。

**E Mathlib 资源**：同 G2 E；另 `Nat.totient_*`、`Real.rpow_le_rpow_left_iff`、`Real.log_le_log`、`Real.add_pow_le_pow_mul_pow_of_sq_le_sq`（不一定需要）。

**F 验收**：`hasChromaticUpperBound_cfpScale` 0 sorry，无外部假设 ⇒ **上界方向达到 Level 3**，这是整个项目第一个真正的渐近结果，应单独在 README 表格新增一行。

**G 工作量**：`Mertens.lean` 1–2k 行（与 G5 共享）+ 上界专用 1–1.5k 行。3–5 周。风险低：所有组合部分已证，只剩分析估计。

---

## §3 推荐顺序与里程碑

| 序 | 项 | 产出 | 为什么这个顺序 |
| :-- | :-- | :-- | :-- |
| 1 | G0 | 文档干净、0 warning | 半天，避免审阅人先被小问题绊倒 |
| 2 | G6 前半：`Erdos298/Mertens.lean` | M1–M4 + 筛法 G 下界 + `minColors_le_of_totient_log` | **已于 2026-09-19 彻底闭合 (18 条无条件引理，0 sorry，0 warning)** |
| 3 | G6 后半 | `hasChromaticUpperBound_cfpScale` | **第一个 Level 3 结果**，README 可以诚实写"上界渐近已无条件闭合" |
| 4 | G4 | Lev ℓ 重定理 + 桥 | 纯组合、确定性最高、不依赖 G1–G3 |
| 5 | G2 | 筛法接口重做 + AP Selberg 筛 | 依赖 Mertens；修掉当前接口的退化 |
| 6 | G3 | Branch B 不回绕子情形 + 论文核对 | 与 G2 联动（回绕问题） |
| 7 | G5 | 参数族 | 依赖 2、4、5、6 |
| 8 | G1 | 结构定理 | 最硬、最不确定；即使做不出来，前 7 步也已把项目推到"下界只剩一个明确命名的结构定理假设"的状态 |

每完成一步：更新 PROGRESS 表格与 README 表格，跑 `#print axioms`，做 §0.3 的空真自检，更新 HANDOVER 的哈希行。

---

## §4 附录

### 4.1 命令速查

```bash
# 只检查一个文件（快）
lake env lean Test.lean

# 全量编译并把日志留下
lake build Erdos298 > build.log 2>&1; echo "exit=$?" >> build.log
grep -c "^warning:" build.log
grep "sorryAx" build.log            # 必须为空
grep "depends on axioms" build.log | grep -v "\[propext, Classical.choice, Quot.sound\]" | grep -v "\[propext, Quot.sound\]"   # 必须为空

# 查 sorry / axiom
grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b" Erdos298.lean Erdos298/*.lean

# 更新 HANDOVER 哈希
sha256sum Erdos298.lean PROGRESS.md
```

### 4.2 空真探测模板

```lean
import Erdos298
open Erdos298

-- 1. 试图反驳一个新接口（能证出来就说明接口错了）
example : ¬ (∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ), ∃ R : CosetAP N,
    smallGrowth T d ⊆ R.toFinset ∧ R.ell * (R.H : Set (ZMod N)).toFinset.card ≤ 128 * d) :=
  not_unguarded_ap_cover'

-- 2. 给一个新结构体造见证（造不出来就不要往下游用）
example : Nonempty CFPArithParams := cfpArithParams_realizable

-- 3. 检查某个"筛法界"是否退化：把 Q := 1 代进去看它是否迫使 C ≥ 1
example (fc) (p : P17FiniteArithConditions fc) (h : HasAPRoughCountBound fc p) :
    (1 : ℝ) ≤ 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ) := by
  have := h.2 ⟨0, 1, by decide, 1⟩ 1 0 (by norm_num) (by simpa using fc.ht_pos)
  simpa [roughCount_one] using this
```

（第 3 条的 `IntAP` 构造子字段顺序为 `a b hb k`，若不匹配请按 `structure IntAP` 调整。）

### 4.3 可复用引理索引（按缺口）

| 缺口 | 直接可用 |
| :-- | :-- |
| G1 | `smallGrowth`, `delta_add_le`, `iterSum_smallGrowth_subset`, `card_smallGrowth_le_div`, `card_smallGrowth_half_le`, `smallGrowth_subset_subgroup`, `proper_subgroup_of_three_coset_absorption`, `closure_card_le_three_of_iterSum_four_le_three`, `mul_128_lt_of_density`, `kneser_bound_all`, `aperiodic_sumset_bound`, `iterSum_card_ge_of_zero_mem_of_generates`, `guardedAPCover_iff_trichotomy` |
| G2 | `erdosBoundingSieve`, `siftedSum_eq_card_remainder`, `card_remainder_le_mainSum_errSum`, `selbergWeight_isUpperMoebius`, `mainSum_selbergWeight_eq`, `errSum_selbergWeight_le`, `selberg_remainder_bound`, `selbergTerms_prime`, `card_filter_dvd_toFinset_le`, `card_filter_natAbs_dvd_toFinset_le`, `roughCount_eq_card_filter_range`, `roughCount_mono`, `coprime_q_W_of_inY_v`, `card_le_sieve_bound_of_cover`, `apCoverSieveBridge_of_cover_and_sieve` |
| G3 | `branchA_AP`, `branchA_AP_k`, `branchA_AP_b_le`, `branchA_AP_cover`, `hasIntAPCoverBranchA`, `intAPCover_of_family`, `intAPCover_of_coset_family`, `scaledCosetAPLift`, `card_le_card_cosetAP_of_image_subset`, `zmod_subgroup_val_dvd`, `zmod_subgroup_scaled_val_dvd`, `subgroup_card_pos`, `subgroup_card_dvd_t` |
| G4 | `lev_pigeonhole_interval`, `sumset_Icc`, `subsetSums_contains_Icc_of_lev`, `mem_subsetSums_of_lev_interval_extend`, `target_hit_of_lev_diverse`, `HasLevIntervalCoverage`, `CFPDiverseWitness.ofLevCoveragePred`, `exists_disjoint_diverse_partition_of_div`, `subsetSumsMod_eq_univ_of_divisor_counts`, `subsetSumsMod_eq_univ_of_isDiverse`, `greedySeq`, `card_greedySeq_E`, `greedySeq_S_subset`, `card_greedySeq_S_succ`, `subsetSums_add_of_disjoint`, `subsetSums_interval_extend`, `card_subsetSums_insert_ge`, `cfp_lemma_5_5`, `cfp_lemma_5_5_scale` |
| G5 | `CFPArithParams`, `P17FiniteArithConditions`, `concreteCFPArithParams`（模板）, `witness_*`（模板）, `inY_v`, `mem_Y_of_mem_Y_v`, `cfpTau_pos`, `cfpScale_pos_of_hyp`, `CFPAsymptoticParams`, `hasChromaticLowerBound_of_asymptotic_params`, `isDiverse_subset_of_card_diff_le`, `subgroupIndex_eq_one_of_isDiverse` |
| G6 | `minColors_le_conlon_fox_pham`, `minColors_le_conlon_fox_pham_coarse`, `cfp_remainder_subset_sieve_remainder`, `selberg_remainder_bound`, `sieveG_ge_one_add_sum_primes`, `minColors_le_of_prime_subset`, `reducedResidues_card_le`, `sieve_primes_card_le`, `HasChromaticUpperBound`, `conlon_fox_pham_bounds` |

### 4.4 Mathlib（rev `db584cd6`）中已确认存在、本手册引用的声明

`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge`, `Chebyshev.theta_ge'`, `Chebyshev.psi_ge`, `Chebyshev.psi_ge'`, `Chebyshev.primeCounting_eq_theta_div_log_add_integral`, `Chebyshev.eventually_primeCounting_le`; `sum_mul_eq_sub_sub_integral_mul`, `sum_mul_eq_sub_integral_mul`（`AbelSummation`）; `harmonic_le_one_add_log`, `log_le_harmonic_floor`; `primorial_le_four_pow`, `primorial_lt_four_pow`, `Nat.Prime.dvd_primorial_iff`, `squarefree_primorial`; `Nat.Primes.summable_rpow`, `Nat.roughNumbersUpTo_card_le'`; `ZMod.cauchy_davenport`; `Finset.ruzsa_covering_mul`; `IsApproximateSubgroup.*`; `Finset.subsetSum`, `Finset.card_succ_choose_two_lt_card_subsetSum_of_pos`; `BoundingSieve.*`（`SelbergSieve.lean`）。**不存在**：Mertens 定理、Deshouillers–Freiman、Freiman 定理、Lev 定理、Szemerédi–Vu/Sárközy 子集和长 AP 定理。
