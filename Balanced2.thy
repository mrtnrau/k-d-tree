theory Balanced2
imports
  Complex_Main
  "Median_Of_Medians_Selection"
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

fun size_kdt :: "kdt \<Rightarrow> nat" where
  "size_kdt (Leaf _) = 1"
| "size_kdt (Node _ _ l r) = size_kdt l + size_kdt r"

fun height_kdt :: "kdt \<Rightarrow> nat" where
  "height_kdt (Leaf _) = 1"
| "height_kdt (Node _ _ l r) = max (height_kdt l) (height_kdt r) + 1"

lemma height_kdt_gt_0:
  "height_kdt kdt > 0"
  by (cases kdt) auto

fun complete_kdt :: "kdt \<Rightarrow> bool" where
  "complete_kdt (Leaf _) = True"
| "complete_kdt (Node _ _ l r) \<longleftrightarrow> complete_kdt l \<and> complete_kdt r \<and> height_kdt l = height_kdt r"

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




fun build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a d ps = (
    if length ps \<le> 1 then
      Leaf (hd ps) 
    else
      let sps = sort_wrt_a a ps in
      let n = length sps div 2 in
      let l = take n sps in
      let g = drop n sps in
      let a' = (a + 1) mod d in
      Node a (hd g ! a) (build' a' d l) (build' a' d g)
  )"

definition build :: "point list \<Rightarrow> kdt" where
  "build ps = build' 0 (dim (hd ps)) ps"




lemma AUX0:
  "set (take n xs) \<union> set (drop n xs) = set xs"
  by (metis append_take_drop_id set_append)

lemma AUX1:
  "length xs \<le> 1 \<Longrightarrow> length xs = 2 ^ k \<Longrightarrow> length xs = 1"
  by (cases xs) auto

lemma AUX2:
  "length xs = 1 \<Longrightarrow> { hd xs } = set xs"
  by (cases xs) auto

lemma AUX3:
  assumes "k > 0"
  shows "(2 :: nat) ^ k div 2 = 2 ^ (k - 1)"
    and "(2 :: nat) ^ k - 2 ^ (k - 1) = 2 ^ (k - 1)"
  using assms by (induction k) auto

lemma AUX4:
  assumes "length xs = 2 ^ k" "k > 0"
  shows "length (take (length xs div 2) xs) = 2 ^ (k - 1)"
    and "length (drop (length xs div 2) xs) = 2 ^ (k - 1)"
  using assms using AUX3 by (induction xs) (auto simp add: min_def)

lemma AUX5:
  assumes "length xs = 2 ^ k" "length xs > 1"
  shows "length (take (length xs div 2) xs) < length xs"
    and "length (drop (length xs div 2) xs) < length xs"
  using assms by (induction xs) auto




lemma build'_set:
  assumes "length ps = 2 ^ k"
  shows "set ps = set_kdt (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    thus ?thesis using "1.prems" AUX1 AUX2
      by (metis set_kdt.simps(1) build'.elims)
  next
    case False

    hence K: "k > 0"
      using "1.prems" gr0I by force
    moreover have "length ?l = 2 ^ (k - 1)" "length ?g = 2 ^ (k - 1)"
      using "1.prems" K AUX4 by fastforce+
    moreover have "length ?l < length ps" "length ?g < length ps"
      using "1.prems" False AUX5 by auto
    ultimately have CHILDREN: "set ?l = set_kdt (build' ?a' d ?l)" "set ?g = set_kdt (build' ?a' d ?g)"
      using 1 by blast+

    have "build' a d ps = Node a (hd ?g ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
      using False by (meson build'.elims not_less)
    moreover have "set ps = set ?l \<union> set ?g"
      using False by (simp add: AUX0)
    ultimately show ?thesis using CHILDREN by simp
  qed
qed




lemma AUX6:
  "distinct ps \<Longrightarrow> distinct (sort_wrt_a a ps)"
  by (induction ps) (auto simp add: distinct_insort)

lemma AUX7:
  "sorted_wrt_a a (sort_wrt_a a ps)"
  apply (induction ps)
  apply (auto)
  using sorted_insort_key sorted_map by fastforce

lemma AUX8:
  assumes "sorted_wrt_a a ps"
  shows "sorted_wrt_a a (take n ps)"
    and "sorted_wrt_a a (drop n ps)"
proof -
  obtain xs ys where "ps = xs @ ys \<and> xs = take n ps \<and> ys = drop n ps"
    by fastforce
  thus "sorted_wrt_a a (take n ps)" "sorted_wrt_a a (drop n ps)" 
    using assms sorted_wrt_append by fastforce+
qed

lemma AUX9:
  "sorted_wrt_a a ps \<Longrightarrow> \<forall>p \<in> set ps. (hd ps)!a \<le> p!a"
  by (induction ps) auto

lemma AUX10:
  assumes "sorted_wrt_a a ps"
  shows "\<forall>t \<in> set (take n ps). \<forall>d \<in> set (drop n ps). t!a \<le> d!a"
proof -
  obtain ts ds where 1: "ps = ts @ ds \<and> ts = take n ps \<and> ds = drop n ps"
    by fastforce
  hence "\<forall>t \<in> set ts. \<forall>d \<in> set ds. t!a \<le> d!a"
    using sorted_wrt_append assms by (metis sorted_wrt_a_def)
  thus ?thesis using 1 by metis
qed

lemma AUX11:
  assumes "sorted_wrt_a a ps" "n < length ps"
  shows "\<forall>t \<in> set (take n ps). t!a \<le> (hd (drop n ps))!a"
  using assms AUX10 by simp




lemma build'_invar:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "a < d"
  shows "invar d (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "hd ?g ! a"

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    hence "length (hd ps) = d"
      using AUX2 "1.prems"(1,2) by (cases ps) auto
    thus ?thesis using True AUX1 by auto
  next
    case False

    have A': "?a' < d"
      using "1.prems"(4) by auto
    moreover have "\<forall>p \<in> set ?l. dim p = d" "\<forall>p \<in> set ?g. dim p = d"
      using "1.prems"(2) in_set_takeD in_set_dropD by force+
    moreover have "distinct ?l" "distinct ?g"
      using "1.prems"(3) AUX6 distinct_take distinct_drop by blast+
    moreover have K: "k > 0"
      using "1.prems" False gr0I by force
    moreover have LEN_GL: "length ?l = 2 ^ (k - 1)" "length ?g = 2 ^ (k - 1)"
      using "1.prems" K AUX4 by fastforce+
    moreover have "length ?l < length ps" "length ?g < length ps"
      using "1.prems" False AUX5 by auto
    ultimately have L: "invar d (build' ?a' d ?l)" and G: "invar d (build' ?a' d ?g)"
      using 1 by blast+

    have "\<forall>p \<in> set ?g. ?disc \<le> p!a"
      using AUX7 AUX8 AUX9 by blast
    hence X: "\<forall>p \<in> set_kdt (build' ?a' d ?g). ?disc \<le> p!a"
      using LEN_GL build'_set by blast

    have "\<forall>p \<in> set ?l. p!a \<le> ?disc"
      using AUX7 AUX11[of a ?sps "(length ?sps div 2)"] by fastforce
    hence Y: "\<forall>p \<in> set_kdt (build' ?a' d ?l). p!a \<le> ?disc"
      using LEN_GL build'_set by blast

    have "set ?l \<inter> set ?g = {}"
      by (metis "1.prems"(3) AUX6 append_take_drop_id distinct_append)
    hence Z: "set_kdt (build' ?a' d ?l) \<inter> set_kdt (build' ?a' d ?g) = {}"
      using LEN_GL build'_set by blast

    have "build' a d ps = Node a (hd ?g ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
      using False by (meson build'.elims not_less)
    thus ?thesis using "1.prems"(4) L G  X Y Z by simp
  qed
qed




lemma AUX12: "k > 0 \<Longrightarrow> 2 * 2 ^ (k - 1) = 2 ^ k"
  by (cases k) auto

lemma AUX13:
  assumes "complete_kdt kdt" 
  shows "size_kdt kdt = 2 ^ (height_kdt kdt - 1)"
  using assms
proof (induction kdt)
  case (Leaf p)
  thus ?case by simp
next
  case (Node a d l r)
  have "size_kdt (Node a d l r) = 2 * 2 ^ (height_kdt l - 1)"
    using Node by simp
  also have "... = 2 ^ height_kdt l"
    using AUX12 height_kdt_gt_0 by auto
  also have "... = 2 ^ (height_kdt (Node a d l r) - 1)"
    using Node by simp
  finally show ?case .
qed

lemma AUX14:
  "(2 :: nat) ^ x = 2 ^ y \<Longrightarrow> x = y"
  by simp

lemma AUX15:
  assumes "complete_kdt kdt1" "complete_kdt kdt2" "size_kdt kdt1 = size_kdt kdt2"
  shows "height_kdt kdt1 = height_kdt kdt2"
proof -
  have "2 ^ (height_kdt kdt1 - 1) = 2 ^ (height_kdt kdt2 - 1)"
    using AUX13 assms by simp
  hence "height_kdt kdt1 - 1 = height_kdt kdt2 - 1"
    using AUX14 by blast
  thus ?thesis using height_kdt_gt_0
    by (metis One_nat_def Suc_pred)
qed




lemma build'_size:
  "length ps = 2 ^ k \<Longrightarrow> size_kdt (build' a d ps) = length ps"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "hd ?g ! a"

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    thus ?thesis using "1.prems"
      by (simp add: antisym)
  next
    case False

    hence "length ?l = 2 ^ (k - 1)" "length ?g = 2 ^ (k - 1)"
      using "1.prems" AUX4 by fastforce+
    moreover have "length ?l < length ps" "length ?g < length ps"
      using "1.prems" False AUX5 by auto
    ultimately have L: "length ?l = size_kdt (build' ?a' d ?l)" and G: "length ?g = size_kdt (build' ?a' d ?g)"
      using "1.IH" by simp_all

    have "length ?l + length ?g = length ps"
      by simp
    moreover have "build' a d ps = Node a (hd ?g ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
      by (meson False build'.elims not_less)
    ultimately show ?thesis using L G by force
  qed
qed




lemma build'_complete:
  "length ps = 2 ^ k \<Longrightarrow> complete_kdt (build' a d ps)"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "hd ?g ! a"

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then show ?thesis by simp
  next
    case False

    hence LEN_LG: "length ?l = 2 ^ (k - 1)" "length ?g = 2 ^ (k - 1)"
      using "1.prems" AUX4 by fastforce+
    moreover have "length ?l < length ps" "length ?g < length ps"
      using "1.prems" False AUX5 by auto
    ultimately have L: "complete_kdt (build' ?a' d ?l)" and G: "complete_kdt (build' ?a' d ?g)"
      using "1.IH" by simp_all

    have "size_kdt (build' ?a' d ?l) = size_kdt (build' ?a' d ?g)"
      using build'_size LEN_LG by auto
    hence "height_kdt (build' ?a' d ?l) = height_kdt (build' ?a' d ?g)"
      using L G AUX15 by blast
    moreover have "build' a d ps = Node a (hd ?g ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
      by (meson False build'.elims not_less)
    ultimately show ?thesis using L G complete_kdt.simps(2) by presburger
  qed
qed




theorem build:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "set ps = set_kdt (build ps)"
    and "size_kdt (build ps) = length ps"
    and "complete_kdt (build ps)"
    and "invar d (build ps)"
  using assms build_def build'_set apply simp
  using assms build_def build'_size apply simp
  using assms build_def build'_complete apply simp
  using assms by (metis build'_invar build_def length_0_conv list.set_sel(1) power_not_zero zero_neq_numeral)

corollary build_height:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "length ps = 2 ^ (height_kdt (build ps) - 1)"
  by (metis AUX13 assms build(2,3))

end