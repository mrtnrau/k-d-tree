theory Balanced
imports
  Complex_Main
  "Median_Of_Medians_Selection.Median_Of_Medians_Selection"
begin




type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym disc = real

datatype kdt =
  Leaf point
| Node axis real kdt kdt


definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

declare dim_def[simp]

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node _ _ l r) = set_kdt l \<union> set_kdt r"

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

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar d (Leaf p) \<longleftrightarrow> dim p = d"
| "invar d (Node a disc l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> disc) \<and> (\<forall>p \<in> set_kdt r. disc \<le> p!a) \<and>
    invar d l \<and> invar d r \<and> a < d \<and> set_kdt l \<inter> set_kdt r = {}"

definition sorted_wrt_a :: "axis \<Rightarrow> point list \<Rightarrow> bool" where
  "sorted_wrt_a a ps = sorted_wrt (\<lambda>p q. p!a \<le> q!a) ps"

declare sorted_wrt_a_def[simp]

definition sort_wrt_a :: "axis \<Rightarrow> point list \<Rightarrow> point list" where
  "sort_wrt_a a ps = sort_key (\<lambda>p. p!a) ps"

declare sort_wrt_a_def[simp]




(* Tree *)

lemma size_ge0[simp]: 
  "0 < size kdt"
  by (induction kdt) auto

lemma eq_size_1[simp]:
  "size kdt = 1 \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  using size_ge0 apply (induction kdt) apply (auto)
  using Balanced.size_ge0 nat_less_le apply blast+
  done

lemma eq_1_size[simp]:
  "1 = size kdt \<longleftrightarrow> (\<exists>p. kdt = Leaf p)"
  using eq_size_1 by metis

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




(* Balanced *)

fun partition :: "axis \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point list * point list * point list" where
  "partition _ _ [] = ([], [], [])"
| "partition a m (p # ps) = (
    let (lt, eq, gt) = partition a m ps in
    if p!a < m then (p # lt, eq, gt)
    else if p!a = m then (lt, p # eq, gt)
    else (lt, eq, p # gt)
  )"

definition partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "partition_by_median a ps = (
     let n = length ps div 2 in
     let ps' = map (\<lambda>p. p!a) ps in
     let m = sort ps' ! n in
     let (lt, eq, gt) = partition a m ps in
     let rem = n - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"

definition fast_partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "fast_partition_by_median a ps = (
     let n = length ps div 2 in
     let ps' = map (\<lambda>p. p!a) ps in
     let m = fast_select n ps' in
     let (lt, eq, gt) = partition a m ps in
     let rem = n - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"




lemma fast:
  "length ps > 0 \<Longrightarrow> fast_partition_by_median a ps = partition_by_median a ps"
  unfolding fast_partition_by_median_def partition_by_median_def
  by (auto simp del: fast_select.simps simp add: fast_select_correct select_def)

lemma partition_filter:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "lt = filter (\<lambda>p. p!a < m) ps"
    and "eq = filter (\<lambda>p. p!a = m) ps"
    and "gt = filter (\<lambda>p. p!a > m) ps"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_length:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "length ps = length lt + length eq + length gt"
    and "length lt + length eq = length (filter (\<lambda>p. p!a \<le> m) ps)"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_set:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "set ps = set lt \<union> set eq \<union> set gt"
    and "set lt \<union> set eq = set (filter (\<lambda>p. p!a \<le> m) ps)"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_by_median_filter:
  assumes "(l, m, r) = partition_by_median a ps" "even (length ps)" "length ps > 0"
  shows partition_by_median_filter_l: "\<forall>p \<in> set l. p!a \<le> m"
    and partition_by_median_filter_r:  "\<forall>p \<in> set r. m \<le> p!a"
  using assms partition_filter
  apply (auto simp add: partition_by_median_def Let_def split: prod.splits)
  apply (smt in_set_takeD in_set_dropD mem_Collect_eq set_filter)+
  done

lemma partition_by_median_length_lr_0:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "length ps = length l + length r"
  using assms partition_length
  apply (auto simp add: partition_by_median_def min_def Let_def split: prod.splits)
  apply (smt add.assoc)+
  done

lemma A:
  assumes "length lt + length eq > k" "length lt \<le> k"
  shows "length (lt @ take (k - length lt) eq) = k"
  using assms by simp

lemma C:
  "length (filter P xs) = length (filter P (sort xs))"
  by (simp add: filter_sort)

lemma A2:
  assumes "k < length xs" "sorted xs"
  shows "k < card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
proof -
  have "\<forall>i. i \<le> k \<longrightarrow> xs ! i \<le> xs ! k"
    using assms sorted_nth_mono by blast
  hence "{i. i \<le> k} \<subseteq> {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    using assms(1) by auto
  moreover have "finite {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    by simp
  ultimately have "card {i. i \<le> k} \<le> card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    using card_mono by blast
  thus ?thesis by simp
qed

lemma A1:
  assumes "k < length xs"
  shows "k < length (filter (\<lambda>x. x \<le> sort xs ! k) xs)"
proof -
  have "k < card {i. i < length (sort xs) \<and> sort xs ! i \<le> sort xs ! k}"
    using assms A2[of k "sort xs"] by simp
  also have "... = length (filter (\<lambda>x. x \<le> sort xs ! k) (sort xs))"
    using length_filter_conv_card[of "\<lambda>x. x \<le> sort xs ! k" "sort xs"] by simp
  also have "... = length (filter (\<lambda>x. x \<le> sort xs ! k) xs)"
    using C by metis
  finally show ?thesis .
qed

lemma B2:
  assumes "k < length xs" "sorted xs"
  shows "card {i. i < length xs \<and> xs ! i < xs ! k} \<le> k"
proof -
  have "\<forall>i. i < length xs \<and> xs!i < xs!k \<longrightarrow> i < k"
    using assms by (meson leD le_less_linear sorted_nth_mono)
  hence "{i. i < length xs \<and> xs ! i < xs ! k} \<subseteq> {i. i < k}"
    by blast
  hence "card {i. i < length xs \<and> xs ! i < xs ! k} \<le> card {i. i < k}"
    using card_mono by blast
  also have "... \<le> k"
    by simp
  finally show ?thesis .
qed

lemma B1:
  assumes "k < length xs"
  shows "length (filter (\<lambda>x. x < sort xs ! k) xs) \<le> k"
proof -
  have "length (filter (\<lambda>x. x < sort xs ! k) xs) = length (filter (\<lambda>x. x < sort xs ! k) (sort xs))"
    using C by blast
  also have "... = card {i. i < length (sort xs) \<and> sort xs ! i < sort xs ! k}"
    using length_filter_conv_card by blast
  also have "... \<le> k"
    using assms B2[of k "sort xs"] by simp
  finally show ?thesis .
qed

lemma D1:
  "length (filter (\<lambda>a. a < k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a < k) ps)"
  by (induction ps) auto

lemma D2:
  "length (filter (\<lambda>a. a \<le> k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a \<le> k) ps)"
  by (induction ps) auto

lemma E:
  assumes "length l = length ps div 2" "length ps = length l + length r"
  shows "length r \<ge> length l" "length r - length l \<le> 1"
  using assms by simp_all

lemma partition_by_median_length_lr_1:
  assumes "(l, m, r) = partition_by_median a ps" "length ps > 0"
  shows "length r - length l \<le> 1" "length r \<ge> length l"
proof -

  let ?n = "length ps div 2"
  let ?ps' = "map (\<lambda>p. p!a) ps"
  let ?m = "sort ?ps' ! ?n"
  let ?leg = "partition a ?m ps"
  let ?lt = "fst ?leg"
  let ?eq = "fst (snd ?leg)"
  let ?gt = "snd (snd ?leg)"
  let ?rem = "?n - length ?lt"
  let ?l = "?lt @ take ?rem ?eq"
  let ?r = "drop ?rem ?eq @ ?gt"

  have "?n < length ?ps'"
    using assms(2) by auto
  hence "length (filter (\<lambda>a. a < ?m) ?ps') \<le> ?n" "length (filter (\<lambda>a. a \<le> ?m) ?ps') > ?n"
    using B1[of ?n ?ps'] A1[of ?n ?ps'] by auto
  hence LN: "length (filter (\<lambda>p. p!a < ?m) ps) \<le> ?n" "length (filter (\<lambda>p. p!a \<le> ?m) ps) > ?n"
    using D1[of ?m a ps] D2[of ?m a ps] by simp_all

  have "(?lt, ?eq, ?gt) = partition a ?m ps"
    by simp
  hence "?lt = filter (\<lambda>p. p!a < ?m) ps" "length ?lt + length ?eq = length (filter (\<lambda>p. p!a \<le> ?m) ps)"
    using partition_filter partition_length by fast+
  hence "length ?lt \<le> ?n" "length ?lt + length ?eq > ?n"
    using LN by simp_all
  hence X: "length ?l = ?n"
    using A by blast

  have Z: "(?l, ?m, ?r) = partition_by_median a ps"
    by (auto simp add: Let_def partition_by_median_def split: prod.splits)
  hence Y: "length ps = length ?l + length ?r"
    using assms partition_by_median_length_lr_0 by blast

  have "length ?r \<ge> length ?l" "length ?r - length ?l \<le> 1"
    using X Y E by blast+
  thus "length r - length l \<le> 1" "length r \<ge> length l" using Z by (metis Pair_inject assms(1))+
qed

lemma partition_by_median_length_lr_2:
  assumes "(l, m, r) = partition_by_median a ps" "even (length ps)" "length ps > 0"
  shows "length l = length r"
  using partition_by_median_length_lr_0 partition_by_median_length_lr_1 assms
  by (metis One_nat_def add.commute diff_is_0_eq even_diff_nat le_SucE le_antisym le_zero_eq odd_one)

lemma partition_by_median_length_lr_3: 
  assumes "(l, m, r) = partition_by_median a ps" "length ps > 1"
  shows "length l < length ps" and "length r < length ps"
  using assms partition_by_median_length_lr_1 partition_by_median_length_lr_2 partition_by_median_length_lr_0
  by (metis add_diff_cancel_left' gr0I less_trans zero_less_diff le_eq_less_or_eq add_diff_cancel_right' leD minus_nat.diff_0)+

lemmas partition_by_median_length = 
  partition_by_median_length_lr_0 partition_by_median_length_lr_1
  partition_by_median_length_lr_2 partition_by_median_length_lr_3

lemma partition_by_median_set:
  "(l, m, r) = partition_by_median a ps \<Longrightarrow> set ps = set l \<union> set r"
  using partition_set
  apply (auto simp add: Let_def partition_by_median_def split: prod.splits)
  apply (smt Un_iff UnCI in_set_takeD in_set_dropD append_take_drop_id set_append)+
  done

function (sequential) build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a d [] = undefined"
| "build' a d [p] = Leaf p" 
| "build' a d ps = (
    let a' = (a + 1) mod d in
    let (l, m, r) = fast_partition_by_median a ps in
    Node a m (build' a' d l) (build' a' d r)
  )"
  by pat_completeness auto
termination build'
  using partition_by_median_length_lr_3
  apply (relation "measure (\<lambda>(a, d, ps). length ps)")
  apply (auto simp add: fast)
  apply fastforce+
  done

lemma build'_simp_1:
  "ps = [p] \<Longrightarrow> build' a d ps = Leaf p"
  by simp

lemma build'_simp_2:
  "ps = p\<^sub>0 # p\<^sub>1 # ps' \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = fast_partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'.simps(3) by (auto simp add: Let_def split: prod.splits)

lemma length_ps_gt_1:
  "length ps > 1 \<Longrightarrow> \<exists>p\<^sub>0 p\<^sub>1 ps'. ps = p\<^sub>0 # p\<^sub>1 # ps'"
  by (induction ps) (auto simp add: neq_Nil_conv)

lemma build'_simp_3:
  "length ps > 1 \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = fast_partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'_simp_2 length_ps_gt_1 by fast

lemmas build'_simps[simp] = build'_simp_1 build'_simp_2 build'_simp_3

declare build'.simps[simp del]

definition build :: "point list \<Rightarrow> kdt" where
  "build ps = build' 0 (dim (hd ps)) ps"




lemma pow2k_pow2k_1:
  assumes "x + y = 2 ^ k" "(x :: nat) = y" "k > 0"
  shows "x = 2 ^ (k - 1)"
    and "y = 2 ^ (k - 1)"
  using assms by (induction k) auto

lemma pow2xy:
  "(2 :: nat) ^ x = 2 ^ y \<Longrightarrow> x = y"
  by simp

lemma build'_set:
  assumes "length ps = 2 ^ k"
  shows "set ps = set_kdt (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence E: "even (length ps)" "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    ultimately have "set ?l = set_kdt (build' ?a' d ?l)" "set ?r = set_kdt (build' ?a' d ?r)" 
      using "1.IH" by simp_all
    moreover have "set ps = set ?l \<union> set ?r"
      using partition_by_median_set fast E by (metis prod.collapse)
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis by auto
  qed
qed




lemma build'_invar:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "a < d"
  shows "invar d (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where P: "ps = [p]"
      using "1.prems" by (cases ps) auto
    hence "dim p = d"
      using "1.prems"(2) by simp
    thus ?thesis using P by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have A': "?a' < d"
      using "1.prems"(4) by auto

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence E: "even (length ps)" and P: "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence PLR: "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast E P by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    moreover have SPLR: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set fast E P by (metis prod.collapse)
    moreover have "distinct ?l" "distinct ?r" and LR: "set ?l \<inter> set ?r = {}"
      using "1.prems"(3) SPLR PLR by (metis card_distinct distinct_append distinct_card length_append set_append)+
    moreover have "\<forall>p \<in> set ?l .dim p = d" "\<forall>p \<in> set ?r .dim p = d"
      using "1.prems"(2) SPLR by simp_all
    ultimately have "invar d (build' ?a' d ?l)" "invar d (build' ?a' d ?r)"
      using "1.IH" A' by simp_all
    moreover have "\<forall>p \<in> set ?l. p ! a \<le> ?m" "\<forall>p \<in> set ?r. ?m \<le> p ! a"
      using partition_by_median_filter E P fast by (metis prod.collapse)+
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using "1.prems"(4) LR L R build'_set by auto
  qed
qed





lemma size_height_kdt:
  assumes "complete kdt" 
  shows "size kdt = 2 ^ (height kdt)"
  using assms
proof (induction kdt)
  case (Leaf p)
  thus ?case by simp
next
  case (Node a d l r)
  have "size (Node a d l r) = 2 * 2 ^ (height l)"
    using Node by simp
  also have "... = 2 ^ (height (Node a d l r))"
    using Node by simp
  finally show ?case .
qed

lemma complete_size_height_kdt:
  assumes "complete kdt1" "complete kdt2" "size kdt1 = size kdt2"
  shows "height kdt1 = height kdt2"
proof -
  have "2 ^ (height kdt1) = 2 ^ (height kdt2)"
    using size_height_kdt assms by simp
  hence "height kdt1 = height kdt2"
    using pow2xy by blast
  thus ?thesis by simp
qed

lemma build'_size:
  assumes "length ps > 0"
  shows "size (build' a d ps) = length ps"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 2: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using "1.prems" partition_by_median_length(1,2,3) fast by (metis prod.collapse)+
    moreover have "length ?l < length ps" "length ?r < length ps"
      using False "1.prems" 2 by auto
    ultimately have "size (build' ?a' d ?l) = length ?l" "size (build' ?a' d ?r) = length ?r" 
      using "1.IH" by simp_all
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using 2 by simp
  qed
qed




lemma build'_complete:
  assumes "length ps = 2 ^ k"
  shows "complete (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence "even (length ps)" "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence PLR: "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    ultimately have CL: "complete (build' ?a' d ?l)" and CR: "complete (build' ?a' d ?r)"
      using "1.IH" by simp_all

    have "size (build' ?a' d ?l) = length ?l" "size (build' ?a' d ?r) = length ?r"
      using L R by (simp_all add: build'_size)
    hence "size (build' ?a' d ?l) = size (build' ?a' d ?r)"
      using PLR(2) by simp
    hence "height (build' ?a' d ?l) = height (build' ?a' d ?r)"
      using CL CR complete_size_height_kdt by blast
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using CL CR by auto
  qed
qed



theorem build:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "set ps = set_kdt (build ps)"
    and "size (build ps) = length ps"
    and "complete (build ps)"
    and "invar d (build ps)"
  using assms build_def build'_set      apply simp
  using assms build_def                 apply (simp add: build'_size)
  using assms build_def build'_complete apply simp
  using assms build_def build'_invar
  by (metis length_0_conv list.set_sel(1) power_not_zero zero_neq_numeral)

corollary build_height:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "length ps = 2 ^ (height (build ps))"
  by (metis assms build(2,3) size_height_kdt)







lemma AUX:
  fixes r :: nat and l :: nat
  assumes "r - l \<le> 1" "r \<ge> l"
  shows "l + 1 = r \<or> l = r"
  using assms by linarith

lemma build'_balanced:
  assumes "length ps > 0"
  shows "balanced (build' a d ps)"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis unfolding balanced_def by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 2: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using partition_by_median_length(1,2,3) fast "1.prems" by (metis prod.collapse)+
    hence 3: "length ?l + 1 = length ?r \<or> length ?l = length ?r"
      using AUX by simp
    moreover have 4: "length ?l < length ps" "length ?r < length ps"
      using False "1.prems" 2(1,2,3) by auto
    moreover have 5: "length ?l > 0" "length ?r > 0"
      using "1.prems" "2"(1) 3 4 by linarith+
    ultimately have B: "balanced (build' ?a' d ?l)" "balanced (build' ?a' d ?r)"
      using "1.IH" by simp_all

    have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    moreover have "size (build' ?a' d ?l) + 1 = size (build' ?a' d ?r) \<or> size (build' ?a' d ?l) = size (build' ?a' d ?r)"
      using 3 5 build'_size by simp
    ultimately show ?thesis using B balanced_Node_if_wbal2 by auto
  qed
qed




lemma complete_if_balanced_size_2powh:
  assumes "balanced kdt" "size kdt = 2 ^ h"
  shows "complete kdt"
proof (rule ccontr)
  assume "\<not> complete kdt"
  hence "2 ^ (min_height kdt) < size kdt" "size kdt < 2 ^ height kdt"
    by (simp_all add: min_height_size_if_incomplete size_height_if_incomplete)
  hence "height kdt - min_height kdt > 1"
    using assms(2) by simp
  hence "\<not> balanced kdt"
    using balanced_def by simp
  thus "False"
    using assms(1) by simp
qed

end