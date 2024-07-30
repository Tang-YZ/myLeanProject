翻译自 [官网文档-simp](https://leanprover-community.github.io/extras/simp.html)
# Simp

## 概述 Overview

在这篇文档中, 将解释 Lean 4 中简化策略 [`simp`](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.simp) 和一个相关的策略[`dsimp`](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html#Lean.Parser.Tactic.dsimp)的基本用法。

这里给了一些指南, 来避免"不可终止的简化`simp`", 并给出 `simp` 和 `dsimp` 的配置选项的简短描述.

## 介绍 Introduction

Lean 中有一个 "化简器", 称作 `simp`, 它参考了一个被称作 *`simp` 引理* 的数据库, 
以(希冀)简化引理和目标. 
这个化简器就是所谓的 **依条件重写项系统** (*conditional term rewriting system*): 
它所作的一切, 就是重复的使用事实 `A = B` 或 `A ↔ B`, 
来用`B`替换(又称**重写***rewrite*)子项中的`A`. 
这个化简器一直愚蠢的重写, 直到不能再进行重写.  
这些 `simp` 引理都是有方向的, 左式 *LHS* 总是被 右式 *RHS* 替代.

理想情况下, 这个数据库将把表达式简化为标准形式。
在实践中, 这通常是无法实现的(标准形式可能不存在, 即便存在, 也可能不存在这样的重写规则集)。
尽管如此, 我们的目标是尽可能接近这一理想。
更好的情况是, 我们希望这个数据库是**合流的** *confluent*，这意味着重写*rewrite*的顺序无关紧要。
与上面的情况同样，我们的目标是尽可能接近合流*confluent*。

虽然这个系统能够完全自动地证明许多简单的语句, 但可能令人失望的事, 它并不能证明所有的简单语句. 

这是一个例子 (使用了 `mathlib` 库).

```lean
import Mathlib.Algebra.Group.Defs

variable (G : Type) [Group G] (a b c : G)

example : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp
```

人通常会解决这样的一个问题呢? 他们会注意到 `a * a⁻¹ = 1`, `1 * 1 = 1`, 等等, 
最后他们把问题简化到了 `b = b`, 这显然是正确的.

这也是化简器的工作流程.  事实上, 如果你在示例 *example* 上, 
添加了 `set_option trace.Meta.Tactic.simp.rewrite true` , 
(在 VS Code中) `simp` 的下方, 将会出现蓝色的波浪状下划线, 
点击它将会向你展示,  `simp` 命令重写的顺序. 

展示如下:
```
[Meta.Tactic.simp.rewrite] @mul_right_inv:1000, a * a⁻¹ ==> 1

[Meta.Tactic.simp.rewrite] @mul_one:1000, 1 * 1 ==> 1

[Meta.Tactic.simp.rewrite] @one_mul:1000, 1 * b ==> b

[Meta.Tactic.simp.rewrite] @mul_inv_cancel_right:1000, b * c * c⁻¹ ==> b

[Meta.Tactic.simp.rewrite] @eq_self:1000, b = b ==> True
```
使用 `simp?` 策略是一个有用的方式, 可以提取出`simp` 使用的引理列.
它建议:
```lean
simp only [mul_right_inv, mul_one, one_mul, mul_inv_cancel_right]
```
这是使用特定的这4个引理, 调用 `simp`.

为了观察那些在简化过程中成功的以及失败的重写，
你可以使用这个更冗长的选项 `set_option trace.Meta.Tactic.simp true`.

## 简化引理 Simp lemmas

那么, 问题来了. Lean 的化简器是怎么知道 `a * a⁻¹ = 1`? 
这是由于 `Mathlib.Algebra.Group.Defs` 中有一个引理, 被打上了标签: `simp`属性*attribute*

```lean
@[simp] lemma mul_right_inv (a : G) : a * a⁻¹ = 1 := ...
```

我们称那些有 `simp` 标签的引理为 "`simp` 引理". 
这是mathlib中, `simp`引理 的更多例子. 

```lean
@[simp] theorem Nat.dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 := ...
@[simp] theorem mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := ...
@[simp] theorem List.mem_singleton {a b : α} : a ∈ [b] ↔ a = b := ...
@[simp] theorem Set.setOf_false : {a : α | False} = ∅ := ...
```

当化简器试图简化一个项 `T` 时, 它会查阅此时系统已知的 `simp` 引理, 当遇到 `A = B` 或 `A ↔ B`
形式的引理时( 其中 `A` 是构成 `T` 的子表达式之一) , 它将用`B` 重写 `T` 中的 `A`, 
然后重新开始. 请注意 `simp` 从最内部的项开始, 然后逐步向外: 它先简化函数的参数, 然后再简化函数.
此外, `simp` 也比较聪明, 可以避免每次都考虑 **所有** 的 `simp` 引理
(现在 `mathlib` 里有超过10000的 `simp` 引理!).

化简器仅仅在一个方向上使用 `simp` 引理: 比如说 `A = B` 是一个 `simp` 引理,
那么 `simp` 将把 `A` 替换成 `B`, 但不把 `B` 替换成 `A`. 因此 `simp` 引理均具有
右式比左式更简单的特性. 这就是说, `=` 和 `↔`在这种情况下将不被视作对称的操作符. 
下面这个例子展现了一个糟糕的 `simp` 引理 (尽管这么写也是被允许的):

```lean
@[simp] lemma mul_right_inv_bad (a : G) : 1 = a * a⁻¹ := ...
```

把 `1` 替换作 `a * a⁻¹` 并不是一个明智的默认方向. 
更糟糕的情况下会让表达式无限增长, 导致 `simp` 无限循环:

```lean
@[simp] lemma even_worse_lemma: (1 : G) = 1 * 1⁻¹ := ...
```

当引入新定义的同时, 一个很常见的做法是, 同时引入 `simp` 引理 来使得表达式保持在一个合理的形式.
mathlib里有一个这样的例子: [data.complex.basic](https://github.com/leanprover-community/mathlib/blob/master/src/data/complex/basic.lean),
它包含了接近100个 `simp` 引理. 尽管他们由定义相等, 像这样的引理也被引入, 
```lean
@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
```
因为这使得 `simp` 拥有**规约/降解** *reduce*表达式的能力并能利用已有的事实. 
以上面的这个为例, 它将复数上的加法转化成了实数上的加法.
如果你允许 `simp` 使用实数加法的交换性, 它将会自动的证明 `(z + w).re = (w + z).re` 
通过`z.re + w.re = w.re + z.re`, 这是复数加法交换性的半个证明.

Lean 的内核本身就是**lambda-演算** *lambda calculus*的一个重写系统, 并且这个系统明确定义了
向前进展*forward process*. 考虑到这一点, 让 `simp` 部分求值表达式, 是一族有用的 `simp` 引理. 
举个例子, 如果你有一个结构体类型 `foo` , 并定义了其类型的一个结构体`myFoo`,
```lean
structure Foo where n : ℕ

def myFoo : Foo where n := 37
```
然后添加了一个 `simp` 引理 `myFoo.n = 37`, 你将赋予化简器计算 `myFoo` 的投影 `Foo.n` 的能力
这样你就不用展开 `myFoo` 的定义了. (默认情况下 `simp` 并不会对大多数定义展开).
由于创造这样的 `simp` 引理实在是太普遍了, 因而有一个[属性*attribute*](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Simps/Basic.html#simpsAttr)
为你自动的创造了他们:
```lean
@[simps] def myFoo : Foo where n := 37
```
这个生成了引理 `@[simp] lemma myFoo_n : myFoo.n = 37`.

## 基本用法 Basic usage

* `simp` 尝试使用Lean此刻已知的所有 `simp` 引理来简化目标.

* `simp [h1, h2]` 使用所有的 `simp` 引理,  以及 `h1` 和 `h2` (既可以是本地的假设, 也可以是没有`simp`标记的其他的引理).

* `simp [← h]` 使用所有的 `simp` 引理, 并反向使用 `h : A = B` 以形式 `B = A` (因此 `simp` 把 `B`重写成 `A`)

* `simp [-thm]` 阻止 `simp` 使用名为 `thm` 的 `simp` 引理.

* `simp [*]` 使用全部的 `simp` 引理, 以及所有的本地假设来简化目标.

* `simp at h` 尝试化简 `h` 使用所有的 `simp` 引理.

* `simp [h1] at h2 ⊢` 尝同时试化简 `h2` 和目标, 使用 `h1` 以及所有的 `simp` 引理 (注意: 字符 `⊢` 使用 `\|-` 或者 `\vdash` 在 VS Code 中打出).

* `simp [*] at *` : 尝试化简目标和所有的假设, 使用所有的 `simp` 引理. 偶尔值得尝试.

* `simp only [h1, h2, ..., hn]` 告知 `simp` 仅仅使用引理 `h1`, `h2`, ..., 而不是全部的 `simp` 引理
(I我们可以在证明的中间使用 `simp only [...]` , 因为随后的 `simp` 集合的改变并不会让证明崩溃.)

* `simp [↓h1]` 使用 `h1` 在进入子项之前. 通常情况下, `simp` 在进入子项后使用引理.

* `simp [↑h1]` 使用 `h1` 在进入子项之后. 这个语法是针对标记有 `simp↓` 的引理使用的.

注意到一些 `simp` 引理有额外的必须满足假设.
举个例子, 一个在等式两边同时消去一个因子的定理, 只有在该因子非零的假设下才有效. 
若 `h` 是一个定理 `P` 的证明并且 `P → A = B` 是一个 `simp` 引理, 那么 `simp [h]` 将把目标中的
`A` 替换成 `B` . `simp` 考虑附加的假设这一事实, 使得它被称作一个 *依条件* 重写项系统. 

## 化简-标准形式 Simp-normal form

有时候有一些不同的方式来称呼同一个东西. 举个例子, 已知 `n : ℕ`, 则假设
 `n ≠ 0`, `0 ≠ n`, `n > 0`, `0 < n`, `1 ≤ n` 以及 `n ≥ 1` 均逻辑等价. 
这可能对化简器这种重写系统造成麻烦, 原因是化简器使用**语法等价** *syntactic equality*来寻找子项. 
如果化简器正在操作项 `T` , 且 `A = B` 是一个 `simp` 引理, 那么, 除非 `T` 的子项 `A'` 和 `A` 
语法上一样 (大致的说: 字面上相同), `simp` 一般而言不会注意到这个引理, 所以它不被被重写为 `B`. 
相似地, 如果自然数 `n` 的非零性(以某种方式表示) 是 `A = B` 形式 `simp` 引理的一个前提,
且 `h` 是 `n` 非零的一个证明 (以另一种方式表示), 那么 `simp [h]` 可能不会把 `A`替换成 `B`.

这个议题*issue*在 `mathlib` 中被解决的方法, 是一劳永逸的固定一个 *`simp` 标准形式* 来表达
(就像是使用 `0 < n` 来表达非零性), 然后在Lean中陈述引理时坚持这种变体. 这就省去了为每个变体
编写重复引理的麻烦. 为了帮助简化器, 很多时候都有规范引理, 把表达式转化成`simp` 标准形式.

一般而言, 如果你正在写一个引理, 你需要知道 "标准形式" 来表达引理. 如果你正在为你自己的定义写引理, 对那些可以用不止一种方式表达的事物写一个标准形式.

`simp` 标准形式的一个例子是, 表达一个类型子集的非空性. 已知 `α : Type` 且 `s : Set α` , 有
`s` 的非空性可以写作 `s.Nonempty` 或者 `s ≠ ∅`. 在 mathlib 中使用 `s.Nonempty` 作为标准形式.

另一个例子: 每一个有限集 `s : Finset α` 可以被强制转化成 `Set α`, 因而 `a : α` 可以写作
`a ∈ s` 或`a ∈ (s : Set α)` 拥有相同的意思. 有限集的属于关系的标准形式是 `a ∈ s`,  
此外有一个标准化 `simp` 引理.
```lean
@[simp] lemma mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s := ...
```
把 `a ∈ (s : Set α)` 转化成正确的标准形式.

因为化简器是从内到外工作的, 简化函数的参数在简化函数之前, 一个 `simp` 引理的函数的参数, 
应当具有标准形式". 举个例子, 若`g 0` 可以被化简, 那么 `@[simp] lemma foo : f (g 0) = 0` 
将永远不会被使用.
Batteries' `simpNF` [linter](https://leanprover-community.github.io/mathlib4_docs/Batteries/Tactic/Lint/Frontend.html) 将检查这件事.
( 把 `#lint` 添加到文件的结尾, 可以为你自己的模块运行mathlib's linters).

## `simpa`

`simpa` 策略是为了完成证明的 `simp` 的一个变体,  -- 作为一个 "结束" 策略, 
如果不能关闭目标将会失败. 基本用法是: 
```lean
simpa [h1, h2] using e
```
此处 `[h1, h2]` 指代 `simp` 引理的可选列表 (和 `simp` 有着相同的语法), `e` 是一个表达式. 
通常而言, `e` 是假设的名字. `e` 的类型和目标都被简化, 并且 `simpa` 成功, 如果他们最终相同. 

这是一个`simpa`的简单例子:
```lean
example (n : ℕ) (h : n + 1 - 1 ≠ 0) : n + 1 ≠ 1 := by
  simpa using h
```
没有 `simpa`, 我们只能 `simp at ⊢ h; exact h`. 所谓的 "非终止的 `simp`", 那些使用了 `simp` 
但没有关闭一个目标, 最好需要避免 (见下章), 而 `simpa` 是避免他们的一个办法.

如果 `using` 从句没有出现, 那么 `simpa` 执行以下三个操作来替代:

1. 目标被化简.
2. 如果一个假设在本地的上下文中, 被命名为 `this` , 那么它的类型也要被化简.
3. `assumption` 策略将被使用.

步骤2是为了支持使用 `simpa` 在 `have : P` 或 `suffices : P`这样的模板之后, 因为
二者默认使用 `this` 作为他们引入的假设的名字.

## 非终止的 `simp` Nonempty simps

`simp` 的行为会随着时间改变, 因为 `simp` 被加入(或移除出)库.  
这意味使用 `simp` 的证明可能会崩溃, 并且, 除非你知道 `simp` 引理集如何变化, 修复证明将会很困难.

举个例子, 如果一个证明形如
```lean
  ...
  simp
  rw [foo_eq_bar]
  ...
```
然后有人把 `@[simp]` 加入到了 `foo_eq_bar` 中, 这个重写将会失效!

虽然在开发初期, 在证明的中间使用`simp`是可行的(所谓的非终止`simp`); 但有一个经验法则是, 
当所有的 `simp` 都完全关闭了目标, 维护 Lean 代码将会变得容易.  
即使这样的 `simp` 在后来崩溃了, 这也确保了我们熟悉预期的目标.

在证明的中间使用 `simp` 我们有以下推荐:

1) `simp only [h1, h2, ..., hn]` 来限制 `simp` 来仅仅使用给定列表的引理, 
因而它不受 `simp` 引理集变化的影响. 诀窍: 使用 `simp?` 在自动生成一个合适的 `simp only`.

2) 使用一个这样的结构 `have h : P := by ...; simp` 来引入一个被 `simp` 证明的引理.
   `have` 表达式也许在证明的中间部分, 但是 `simp` 关闭了它引入的假设.
   
3) 如果 `simp` 把目标转化成了 `P`, 这样你就可以这样写: 
```lean
  suffices : P by simpa
```
这在当前目标之后增加了一个新目标 `P` , 并在后面引入了一个新的假设 `this : P`, 同时简化了目标和
`this`, 并企图使用 `this` 关闭原目标. `simpa` 策略**需要**目标被关闭, 这点与 `simp` 不同, 
当它崩溃时将很容易知道. 源代码中显式的 `P` 将有助于修复代码.

非终止的 `simp` 可以以这样的策略列的形式出现在证明的途中 `simp at ⊢ h; exact h`.
因为这可以被这个代替 `simpa using h`.

## `dsimp`

`dsimp` 是 `simp` 的变种, 仅仅使用 "定义上的" `simp` 引理. 即等式两边由定义相等, 
可以使用 `rfl` 或者 `Iff.rfl`证明的 `simp` 引理.

类似于 `simp`, 在证明的中间不推荐使用它. 不过, 如果 `dsimp` 把你的目标转化成了 `h` , 
那策略 `change h` 将会做到同样的事情. `dsimp` 的另一个用法是
```lean
dsimp only
```
是 `dsimp only []` 的缩写, 是不添加任何 `simp` 引理的 `dsimp` .
这可以在证明的中间安全的使用, 而且也是一个有用的写法来整理目标: 除此之外, 它也对lambda表达式
做beta 规约(it will turn `(fun x => f x) 37` into `f 37`), 同时也将化结构体的投影
(it will turn `{ toFun := f, ... }.toFun` into `f`).

## 更高级的功能 More advanced features

### 释放器 Discharger

Lean 有如下的定理:

```lean
theorem Nat.max_eq_left {a b : ℕ} (h : b ≤ a) : max a b = a
```

然而, `simp` 仅仅使用这个定理不能证明下面这个目标.

```lean
example : max (1 : ℕ) 0 = 1 := by
  simp only [Nat.max_eq_left]
-- simp made no progress
```

这是因为 `simp` 不能证明这个附加条件 `(0 : ℕ) ≤ 1`; 可以通过命令查看
`set_option trace.Meta.Tactic.simp.discharge true`.

```lean
[Meta.Tactic.simp.discharge] @Nat.max_eq_left discharge ❌
      0 ≤ 1
```

这个附加条件可以使用 `decide` 来实现:

```lean
example : (0 : ℕ) ≤ 1 := by
  decide
```

如何在 `simp` 中使用这个策略来解决边界条件? 这是答案:

```lean
example : max (1 : ℕ) 0 = 1 := by
  simp (disch := decide) only [Nat.max_eq_left] --译者注:disch是discharger的缩写
```


### 完整语法 Full syntax

这是 `dsimp` 策略的完整语法:

> `dsimp` (`?`)? (`!`)? (`(config :=` config `)`)? (`(disch :=` discharger `)`)? (`only`)? (`[`list of lemmas`]`)? (`at` locations)?

其中 "( ... )?" 意味着表达式的可选部分, 并且 "|" 提供了互斥的选项. 引理列与 `rw` 类似, 
但是附加的 `-lemma_name` 意为着这个引理被排除出使用的 `simp` 引理之外.配置选项将在下一节中描述.

若 `!` 出现, 它在配置选项中添加了 `autoUnfold := true` .
若 `?` 出现, 它会让 `simp` 给出需要用到的 `simp` 引理列.

这是 `simp` 策略的完整语法:

> `simp` (`?`)? (`!`)? (`(config :=` config `)`)? (`(disch :=` discharger `)`)? (`only`)? (`[`list of `*` and lemmas`]`)? (`at` locations)?

这是 `simpa` 策略的完整语法:

> `simpa` (`?`)? (`!`)? (`(config :=` config `)`)? (`(disch :=` discharger `)`)? (`only`)? (`[`list of `*` and lemmas`]`)? (`using` expr)?

它的意思和 `simp` 一样, 但 `using` 可以给任何的表达式, 并不仅仅是 `at` 一个本地常量.

### 自定义化简属性 Custom simp attributes

使用命令 [`register_simp_attr`](https://leanprover-community.github.io/mathlib_docs/commands.html#mk_simp_attribute),(译者注: 怎么这个链接是mathlib3, 是不是过时了)
你可以使用你自己的 `@[simp]`-类似于属性, 但是关键字不同:
打着这个新标签 `@[new_attr]` 的引理并 _不在_ `simp` 引理的默认集合中.
事实上, 他们需要被显示的包含: `simp [new_attr]`. 这通常可以取代冗长的 `simp only [...]` 调用, 
并使得代码更易读. 一般用法的一些例子是
[`mfld_simps`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Attr/Register.html#Parser.Attr.mfld_simps),
and [`field_simps`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Attr/Register.html#Parser.Attr.field_simps).

### 配置选项 Configuration options

`simp` 和 `dsimp` 都可以添加额外的配置选项使用记录record的语法.
举个例子, `simp (config := { singlePass := true })` 在 `singlePass` 配置设为真时运行 `simp` 
我们可以使用 `singlePass` 来避免可能出现的循环.

Lean 的内核文件 `Init/MetaTypes.lean` 显示了其他的配置选项结构体 [`Lean.Meta.DSimp.Config`](https://leanprover-community.github.io/mathlib4_docs/Init/MetaTypes.html#Lean.Meta.DSimp.Config) 以及 [`Lean.Meta.Simp.Config`](https://leanprover-community.github.io/mathlib4_docs/Init/MetaTypes.html#Lean.Meta.Simp.Config) .
他们中的大多数并不是和普通用户很相关, 甚至有一些并未完整的写在文档里!
下表中再现了这些选项, 其中在相应的列中给出了`simp` 以及 `dsimp` 的配置选项的默认值. 
-- 如果没有默认值, 则该选项不可用。
"max" 默认值即 `Lean.Meta.Simp.defaultMaxSteps`, 目前是 `100000`.

(译者注: 为了区分和直观性, 我把专有名词之外的reduce翻译成了降解)
| 选项 | `simp` | `dsimp` | 描述 |
| --- | --- | --- | --- |
| `maxSteps` | max | | 失败前允许的最大步数 |
| `maxDischargeDepth` | 2 | | 对前提条件进行简化的最大递归深度 |
| `contextual` | `false` | | 使用附加的 `simp` 引理, 基于当前子表达式的上下文 (例子见下)  |
| `memoize` | `true` | | 对子项的化简, 执行缓存 |
| `singlePass` | `false` | | 对每一个子项最多访问一次 |
| `zeta` | `true` | `true` | 进行 zeta-规约: `let x := a; b` ↝ `b[x := a]` |
| `beta` | `true` | `true` | 进行 beta-规约: `(fun x => a) y` ↝ `a[x := y]` |
| `eta` | `true` | `true` | 允许 eta-等价: `(fun x => f x)` ↝ `f` (目前正在开发) |
| `etaStruct` | `.all` | `.all` | 配置如何确定两个结构实例之间的定义相等性. 请参阅文档 [`Lean.Meta.EtaStructMode`](https://leanprover-community.github.io/mathlib4_docs/Init/MetaTypes.html#Lean.Meta.EtaStructMode) |
| `iota` | `true` | `true` | 递归子降解: `Nat.recOn (succ n) Z R` ↝ `R n (Nat.recOn n Z R)` |
| `proj` | `true` | `true` | 投影降解: `Prod.fst (a, b)` ↝ `a` |
| `decide` | `false` | `false` | 把命题 `p` 重写为 `True` 或 `False` 通过推断 `Decidable p` 的实例并降解 |
| `arith` | `false` | | 化简简单的算术表达式 |
| `autoUnfold` | `false` | `false` | 使用由等式编译器生成的所有等式引理进行降解 |
| `dsimp` | `true` | | 当 `true` 时, 则对依赖参数dependent argument使用`dsimp`, 如果没有允许 `simp` 访问他们适合的定理. 当 `dsimp` 参数为 `false`, 参数将不被访问. |(译者没有看懂)
| `failIfUnchanged` | `true` | `true` | 如果简化没有进展则报错 |
| `ground` | `false` | | 降解基项 ground term. 当一个项不包含自由变量或者元变量时被称作基项. |
| `unfoldPartialApp` | `false` | `false` |当我们需要展开 `f` 时, 展开 `f` 即使它仅仅被部分应用(译者注: 没有传够参数?)|
| `zetaDelta` | `false` | `false` | 展开本地的定义. 即, 包含条目 `x : t := e` 的上下文, 把自由变量 `x` 降解到 `e`. |

`autoUnfold` 添加的等式型引理,  由等式/模式匹配编译器生成.

`contextual` 选项使得 `simp` 拥有能力考虑根据子表达式周围的上下文, 添加的 `simp` 引理.
举个例子, 他可以通过临时性的添加"隐含→"的前件作为 `simp` 引理来化简后件. 对下面的例子很有必要:
```lean
example {x y : ℕ} : x = 0 → y = 0 → x = y := by
  simp (config := { contextual := true })
```
