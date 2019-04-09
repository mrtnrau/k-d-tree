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




(* Tree *)

lemma size_ge0[simp]: 
  "0 < size kdt"
  by (induction kdt) auto

lemma eq_size_0[simp]: 
  "size (Leaf p) = 1"
  by simp

lemma eq_0_size[simp]: 
  "1 = size (Leaf p)"
  by simp

lemma neq_Leaf_iff: 
  "(\<nexists>p. kdt = Leaf p) = (\<exists>a s l r. kdt = Node a s l r)"
  by (cases kdt) auto

lemma eq_height_0[simp]: 
  "height kdt = 0 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_0_height[simp]: 
  "0 = height kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_min_height_0[simp]: 
  "min_height kdt = 0 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma eq_0_min_height[simp]: 
  "0 = min_height kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  by (cases kdt) auto

lemma size_height: 
  "size kdt \<le> 2 ^ height kdt"
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

lemma min_height_le_height: 
  "min_height kdt \<le> height kdt"
  by (induction kdt) auto

lemma min_height_size: 
  "2 ^ min_height kdt \<le> size kdt"
proof(induction kdt)
  case (Node a s l r)
  have "(2::nat) ^ min_height (Node a s l r) \<le> 2 ^ min_height l + 2 ^ min_height r"
    by (simp add: min_def)
  also have "\<dots> \<le> size (Node a s l r)" using Node.IH by simp
  finally show ?case .
qed simp

lemma complete_iff_height: 
  "complete kdt \<longleftrightarrow> (min_height kdt = height kdt)"
  apply (induction kdt)
  apply simp
  apply (simp add: min_def max_def)
  by (metis le_antisym le_trans min_height_le_height)

lemma size_if_complete: 
  "complete kdt \<Longrightarrow> size kdt = 2 ^ height kdt"
  by (induction kdt) auto

lemma complete_if_size_height: 
  "size kdt = 2 ^ height kdt \<Longrightarrow> complete kdt"
proof (induction "height kdt" arbitrary: kdt)
  case 0 thus ?case by auto
next
  case (Suc h)
  hence "\<nexists>p. kdt = Leaf p"
    by auto
  then obtain a s l r where [simp]: "kdt = Node a s l r"
    using neq_Leaf_iff by auto
  have 1: "height l \<le> h" and 2: "height r \<le> h" using Suc(2) by(auto)
  have 3: "\<not> height l < h"
  proof
    assume 0: "height l < h"
    have "size kdt = size l + size r" by simp
    also have "\<dots> \<le> 2 ^ height l + 2 ^ height r"
      using size_height[of l] size_height[of r] by arith
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
      using size_height[of l] size_height[of r] by arith
    also have " \<dots> < 2 ^ height l + 2 ^ h" using 0 by (simp)
    also have " \<dots> \<le> 2 ^ h + 2 ^ h" using 1 by (simp)
    also have "\<dots> = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally have "size kdt < size kdt" .
    thus False by (simp)
  qed
  from 1 2 3 4 have *: "height l = h" "height r = h" by linarith+
  hence "size l = 2 ^ height l" "size r = 2 ^ height r"
    using Suc(3) size_height[of l] size_height[of r] by (auto)
  with * Suc(1) show ?case by simp
qed

lemma complete_if_size_min_height: 
  "size kdt = 2 ^ min_height kdt \<Longrightarrow> complete kdt"
proof (induct "min_height kdt" arbitrary: kdt)
  case 0 thus ?case by auto
next
  case (Suc h)
  hence "\<nexists>p. kdt = Leaf p"
    by auto
  then obtain a s l r where [simp]: "kdt = Node a s l r"
    using neq_Leaf_iff by auto
  have 1: "h \<le> min_height l" and 2: "h \<le> min_height r" using Suc(2) by (auto)
  have 3: "\<not> h < min_height l"
  proof
    assume 0: "h < min_height l"
    have "size kdt = size l + size r" by simp
    also note min_height_size[of l]
    also(xtrans) note min_height_size[of r]
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
    also note min_height_size[of l]
    also(xtrans) note min_height_size[of r]
    also(xtrans) have "(2::nat) ^ min_height r > 2 ^ h"
        using 0 by (simp add: diff_less_mono)
    also(xtrans) have "(2::nat) ^ min_height l \<ge> 2 ^ h" using 1 by simp
    also(xtrans) have "(2::nat) ^ h + 2 ^ h = 2 ^ (Suc h)" by (simp)
    also have "\<dots> = size kdt" using Suc(2,3) by simp
    finally show False by (simp add: diff_le_mono)
  qed
  from 1 2 3 4 have *: "min_height l = h" "min_height r = h" by linarith+
  hence "size l = 2 ^ min_height l" "size r = 2 ^ min_height r"
    using Suc(3) min_height_size[of l] min_height_size[of r] by (auto)
  with * Suc(1) show ?case
    by (simp add: complete_iff_height)
qed

lemma complete_iff_size: 
  "complete kdt \<longleftrightarrow> size kdt = 2 ^ height kdt"
  using complete_if_size_height size_if_complete by blast

lemma size_height_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> size kdt < 2 ^ height kdt"
  by (meson antisym_conv complete_iff_size not_le size_height)

lemma min_height_size_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> 2 ^ min_height kdt < size kdt"
  by (metis complete_if_size_min_height le_less min_height_size)

lemma balanced_subtreeL: 
  "balanced (Node a s l r) \<Longrightarrow> balanced l"
  by (simp add: balanced_def)

lemma balanced_subtreeR: 
  "balanced (Node a s l r) \<Longrightarrow> balanced r"
  by (simp add: balanced_def)

lemma balanced_optimal:
  assumes "balanced kdt" "size kdt \<le> size kdt'"
  shows "height kdt \<le> height kdt'"
proof (cases "complete kdt")
  case True
  have "(2::nat) ^ height kdt \<le> 2 ^ height kdt'"
  proof -
    have "2 ^ height kdt = size kdt"
      using True by (simp add: complete_iff_height size_if_complete)
    also have "\<dots> \<le> size kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'" by (rule size_height)
    finally show ?thesis .
  qed
  thus ?thesis by (simp)
next
  case False
  have "(2::nat) ^ min_height kdt < 2 ^ height kdt'"
  proof -
    have "(2::nat) ^ min_height kdt < size kdt"
      by(rule min_height_size_if_incomplete[OF False])
    also have "\<dots> \<le> size kdt'" using assms(2) by simp
    also have "\<dots> \<le> 2 ^ height kdt'"  by(rule size_height)
    finally have "(2::nat) ^ min_height kdt < (2::nat) ^ height kdt'" .
    thus ?thesis .
  qed
  hence *: "min_height kdt < height kdt'" by simp
  have "min_height kdt + 1 = height kdt"
    using min_height_le_height[of kdt] assms(1) False
    by (simp add: complete_iff_height balanced_def)
  with * show ?thesis by arith
qed

(* Tree_Real *)

lemma size_height_log: 
  "log 2 (size kdt) \<le> height kdt"
  by (simp add: log2_of_power_le size_height)

lemma min_height_size_log: 
  "min_height kdt \<le> log 2 (size kdt)"
  by (simp add: le_log2_of_power min_height_size)

lemma size_log_if_complete: 
  "complete kdt \<Longrightarrow> height kdt = log 2 (size kdt)"
  by (simp add: log2_of_power_eq size_if_complete)

lemma min_height_size_log_if_incomplete:
  "\<not> complete kdt \<Longrightarrow> min_height kdt < log 2 (size kdt)"
  by (simp add: less_log2_of_power min_height_size_if_incomplete)

lemma min_height_balanced: 
  assumes "balanced kdt"
  shows "min_height kdt = nat(floor(log 2 (size kdt)))"
proof cases
  assume *: "complete kdt"
  hence "size kdt = 2 ^ min_height kdt"
    by (simp add: complete_iff_height size_if_complete)
  from log2_of_power_eq[OF this] show ?thesis by linarith
next
  assume *: "\<not> complete kdt"
  hence "height kdt = min_height kdt + 1"
    using assms min_height_le_height[of kdt]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size kdt < 2 ^ (min_height kdt + 1)"
    by (metis * size_height_if_incomplete)
  hence "log 2 (size kdt) < min_height kdt + 1"
    using log2_of_power_less size_ge0 by blast
  thus ?thesis using min_height_size_log[of kdt] by linarith
qed

lemma height_balanced: 
  assumes "balanced kdt"
  shows "height kdt = nat(ceiling(log 2 (size kdt)))"
proof cases
  assume *: "complete kdt"
  hence "size kdt = 2 ^ height kdt"
    by (simp add: size_if_complete)
  from log2_of_power_eq[OF this] show ?thesis
    by linarith
next
  assume *: "\<not> complete kdt"
  hence **: "height kdt = min_height kdt + 1"
    using assms min_height_le_height[of kdt]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size kdt \<le> 2 ^ (min_height kdt + 1)" by (metis size_height)
  from  log2_of_power_le[OF this size_ge0] min_height_size_log_if_incomplete[OF *] **
  show ?thesis by linarith
qed

lemma balanced_Node_if_wbal1:
  assumes "balanced l" "balanced r" "size l = size r + 1"
  shows "balanced (Node a s l r)"
proof -
  from assms(3) have [simp]: "size l = size r + 1" by simp
  have "nat \<lceil>log 2 (1 + size r)\<rceil> \<ge> nat \<lceil>log 2 (size r)\<rceil>"
    by(rule nat_mono[OF ceiling_mono]) simp
  hence 1: "height(Node a s l r) = nat \<lceil>log 2 (1 + size r)\<rceil> + 1"
    using height_balanced[OF assms(1)] height_balanced[OF assms(2)]
    by (simp del: nat_ceiling_le_eq add: max_def)
  have "nat \<lfloor>log 2 (1 + size r)\<rfloor> \<ge> nat \<lfloor>log 2 (size r)\<rfloor>"
    by(rule nat_mono[OF floor_mono]) simp
  hence 2: "min_height(Node a s l r) = nat \<lfloor>log 2 (size r)\<rfloor> + 1"
    using min_height_balanced[OF assms(1)] min_height_balanced[OF assms(2)]
    by (simp)
  have "size r \<ge> 1" by (simp add: Suc_leI)
  then obtain i where i: "2 ^ i \<le> size r" "size r < 2 ^ (i + 1)"
    using ex_power_ivl1[of 2 "size r"] by auto
  hence i1: "2 ^ i < size r + 1" "size r + 1 \<le> 2 ^ (i + 1)" by auto
  from 1 2 floor_log_nat_eq_if[OF i] ceiling_log_nat_eq_if[OF i1]
  show ?thesis by(simp add:balanced_def)
qed

lemma balanced_sym: 
  "balanced (Node a s l r) \<Longrightarrow> balanced (Node a' s' r l)"
  by (auto simp: balanced_def)

lemma balanced_Node_if_wbal2:
  assumes "balanced l" "balanced r" "abs(int(size l) - int(size r)) \<le> 1"
  shows "balanced (Node a s l r)"
proof -
  have "size l = size r \<or> (size l = size r + 1 \<or> size r = size l + 1)" (is "?A \<or> ?B")
    using assms(3) by linarith
  thus ?thesis
  proof
    assume "?A"
    thus ?thesis using assms(1,2)
      apply(simp add: balanced_def min_def max_def)
      by (metis assms(1,2) balanced_optimal le_antisym le_less)
  next
    assume "?B"
    thus ?thesis
      by (meson assms(1,2) balanced_sym balanced_Node_if_wbal1)
  qed
qed

end