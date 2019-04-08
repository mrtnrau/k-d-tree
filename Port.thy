theory Port
  imports Complex_Main
begin

type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym disc = real

datatype kdt =
  Leaf point
  | Node axis real kdt kdt




fun size :: "kdt \<Rightarrow> nat" where
  "size (Leaf _) = 1"
| "size (Node _ _ l r) = size l + size r"

fun height :: "kdt \<Rightarrow> nat" where
  "height (Leaf _) = 0"
| "height (Node _ _ l r) = max (height l) (height r) + 1"

fun min_height :: "kdt \<Rightarrow> nat" where
  "min_height (Leaf _) = 0"
| "min_height (Node _ _ l r) = min (min_height l) (min_height r) + 1"

definition balanced :: "kdt \<Rightarrow> bool" where
  "balanced kdt \<longleftrightarrow> height kdt - min_height kdt \<le> 1"

fun complete :: "kdt \<Rightarrow> bool" where
  "complete (Leaf _) = True"
| "complete (Node _ _ l r) \<longleftrightarrow> complete l \<and> complete r \<and> height l = height r"




lemma size_ge0[simp]: "0 < size t"
  by (induction t) auto

lemma height_le_size_tree: "height kdt \<le> size kdt"
  apply (induction kdt)
  apply (auto simp add: max_def)
  apply (metis Suc_diff_le Suc_leI diff_is_0_eq' le_add2 le_antisym le_diff_conv not_less_eq_eq size_ge0)
  by (meson add_mono_thms_linordered_field(4) dual_order.trans not_add_less1 not_less_eq_eq size_ge0)

lemma size1_height: "size kdt \<le> 2 ^ height kdt"
proof(induction kdt)
  case (Node a s l r)
  show ?case
  proof (cases "height l \<le> height r")
    case True
    have "size (Node a s l r) = size l + size r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r" using Node.IH by arith
    also have "\<dots> \<le> 2 ^ height r + 2 ^ height r" using True by simp
    also have "\<dots> = 2 ^ height (Node a s l r)"
      using True by (auto simp: max_def mult_2)
    finally show ?thesis .
  next
    case False
    have "size (Node a s l r) = size l + size r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r" using Node.IH by arith
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height l" using False by simp
    finally show ?thesis using False by (auto simp: max_def mult_2)
  qed
qed simp

lemma min_height_le_height: "min_height kdt \<le> height kdt"
  by (induction kdt) auto

lemma min_height_size1: "2 ^ min_height kdt \<le> size kdt"
proof(induction kdt)
  case (Node a s l r)
  have "(2::nat) ^ min_height (Node a s l r) \<le> 2 ^ min_height l + 2 ^ min_height r"
    by (simp add: min_def)
  also have "\<dots> \<le> size (Node a s l r)" using Node.IH by simp
  finally show ?case .
qed simp

lemma complete_iff_height: "complete kdt \<longleftrightarrow> (min_height kdt = height kdt)"
  apply(induction kdt)
  apply simp
  apply (simp add: min_def max_def)
  by (metis le_antisym le_trans min_height_le_height)

lemma size1_if_complete: "complete kdt \<Longrightarrow> size kdt = 2 ^ height kdt"
  by (induction kdt) auto

lemma complete_if_size1_height: "size kdt = 2 ^ height kdt \<Longrightarrow> complete kdt"
proof (induction "height kdt" arbitrary: kdt)
  case 0 thus ?case
    by (metis complete_iff_height le_zero_eq min_height_le_height)
next
  case (Suc h)
  then obtain a s l r where [simp]: "kdt = Node a s l r"
    by (metis Suc.hyps(2) Zero_not_Suc height.elims)
  have 1: "height l \<le> h" and 2: "height r \<le> h" using Suc(2) by(auto)
  have 3: "\<not> height l < h"
  proof
    assume 0: "height l < h"
    have "size kdt = size l + size r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r"
      using size1_height[of l] size1_height[of r] by arith
    also have " \<dots> < 2 ^ h + 2 ^ height r" using 0 by (simp)
    also have " \<dots> \<le> 2 ^ h + 2 ^ h" using 2 by (simp)
    also have "\<dots> = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally have "size kdt < size kdt" .
    thus False by (simp)
  qed
  have 4: "\<not> height r < h"
  proof
    assume 0: "height r < h"
    have "size kdt = size l + size r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r"
      using size1_height[of l] size1_height[of r] by arith
    also have " \<dots> < 2 ^ height l + 2 ^ h" using 0 by (simp)
    also have " \<dots> \<le> 2 ^ h + 2 ^ h" using 1 by (simp)
    also have "\<dots> = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally have "size kdt < size kdt" .
    thus False by (simp)
  qed
  from 1 2 3 4 have *: "height l = h" "height r = h" by linarith+
  hence "size l = 2 ^ height l" "size r = 2 ^ height r"
    using Suc(3) size1_height[of l] size1_height[of r] by (auto)
  with * Suc(1) show ?case by simp
qed

lemma complete_if_size1_min_height: "size kdt = 2 ^ min_height kdt \<Longrightarrow> complete kdt"
proof (induct "min_height kdt" arbitrary: kdt)
  case 0 thus ?case
    by (metis add_is_0 complete.simps(1) min_height.elims one_neq_zero)
next
  case (Suc h)
  then obtain a s l r where [simp]: "kdt = Node a s l r"
    by (metis Zero_not_Suc min_height.elims)
  have 1: "h \<le> min_height l" and 2: "h \<le> min_height r" using Suc(2) by(auto)
  have 3: "\<not> h < min_height l"
  proof
    assume 0: "h < min_height l"
    have "size kdt = size l + size r" by simp
    also note min_height_size1[of l]
    also(xtrans) note min_height_size1[of r]
    also(xtrans) have "(2::nat) ^ min_height l > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height r \<ge> 2 ^ h" using 2 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  have 4: "\<not> h < min_height r"
  proof
    assume 0: "h < min_height r"
    have "size kdt = size l + size r" by simp
    also note min_height_size1[of l]
    also(xtrans) note min_height_size1[of r]
    also(xtrans) have "(2::nat) ^ min_height r > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height l \<ge> 2 ^ h" using 1 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  from 1 2 3 4 have *: "min_height l = h" "min_height r = h" by linarith+
  hence "size l = 2 ^ min_height l" "size r = 2 ^ min_height r"
    using Suc(3) min_height_size1[of l] min_height_size1[of r] by (auto)
  with * Suc(1) show ?case
    by (simp add: complete_iff_height)
qed

lemma complete_iff_size1: "complete kdt \<longleftrightarrow> size kdt = 2 ^ height kdt"
  using complete_if_size1_height size1_if_complete by blast

lemma size1_height_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> size kdt < 2 ^ height kdt"
  by (meson antisym_conv complete_iff_size1 not_le size1_height)

lemma min_height_size1_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> 2 ^ min_height kdt < size kdt"
  by (metis complete_if_size1_min_height le_less min_height_size1)

lemma balanced_subtreeL: "balanced (Node a s l r) \<Longrightarrow> balanced l"
  by (simp add: balanced_def)

lemma balanced_subtreeR: "balanced (Node a s l r) \<Longrightarrow> balanced r"
  by (simp add: balanced_def)

lemma balanced_optimal:
  fixes kdt :: kdt and kdt' :: kdt
  assumes "balanced kdt" "size kdt \<le> size kdt'"
  shows "height kdt \<le> height kdt'"
proof (cases "complete kdt")
  case True
  have "(2::nat) ^ height kdt \<le> 2 ^ height kdt'"
  proof -
    have "2 ^ height kdt = size kdt"
      using True by (simp add: complete_iff_height size1_if_complete)
    also have "\<dots> \<le> size kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'" by (rule size1_height)
    finally show ?thesis .
  qed
  thus ?thesis by (simp)
next
  case False
  have "(2::nat) ^ min_height kdt < 2 ^ height kdt'"
  proof -
    have "(2::nat) ^ min_height kdt < size kdt"
      by(rule min_height_size1_if_incomplete[OF False])
    also have "\<dots> \<le> size kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'"  by(rule size1_height)
    finally have "(2::nat) ^ min_height kdt < (2::nat) ^ height kdt'" .
    thus ?thesis .
  qed
  hence *: "min_height kdt < height kdt'" by simp
  have "min_height kdt + 1 = height kdt"
    using min_height_le_height[of kdt] assms(1) False
    by (simp add: complete_iff_height balanced_def)
  with * show ?thesis by arith
qed

end
