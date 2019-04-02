theory Balanced2
imports
  Complex_Main
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

fun complete_kdt :: "kdt \<Rightarrow> bool" where
  "complete_kdt (Leaf _) = True"
| "complete_kdt (Node _ _ l r) \<longleftrightarrow> complete_kdt l \<and> complete_kdt r \<and> height_kdt l = height_kdt r"

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar d (Leaf p) \<longleftrightarrow> dim p = d"
| "invar d (Node a disc l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> disc) \<and> (\<forall>p \<in> set_kdt r. disc \<le> p!a) \<and>
    invar d l \<and> invar d r \<and> a < d"

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
      Node a (last l ! a) (build' a' d l) (build' a' d g)
  )"




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

    have "build' a d ps = Node a (last ?l ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
      using False by (meson build'.elims not_less)
    moreover have "set ps = set ?l \<union> set ?g"
      using False by (simp add: AUX0)
    ultimately show ?thesis using CHILDREN by simp
  qed
qed

lemma build'_invar_single:
  "length ps = 1 \<Longrightarrow> \<forall>p \<in> set ps. dim p = d \<Longrightarrow> distinct ps \<Longrightarrow> a < d \<Longrightarrow> invar d (build' a d ps)"
  apply (auto)
  by (metis hd_in_set length_0_conv nat.distinct(1))

lemma aux_d:
  "distinct ps \<Longrightarrow> distinct (sort_wrt_a a ps)"
  apply (induction ps)
   apply (auto simp add: distinct_insort)
  done

lemma aux_ss:
  "sorted_wrt_a a (sort_wrt_a a ps)"
  apply (induction ps)
   apply (auto)
  using sorted_insort_key sorted_map by fastforce

lemma aux_s:
  assumes "sorted_wrt_a a ps"
  shows "sorted_wrt_a a (take n ps)"
    and "sorted_wrt_a a (drop n ps)"
proof -
  obtain xs ys where "ps = xs @ ys \<and> xs = take n ps \<and> ys = drop n ps"
    by fastforce
  thus "sorted_wrt_a a (take n ps)" 
   and "sorted_wrt_a a (drop n ps)" using assms sorted_wrt_append
    by fastforce+
qed

lemma aux_sss:
  "sorted_wrt_a a ps \<Longrightarrow> \<forall>p \<in> set ps. p!a \<le> (last ps)!a"
  apply (induction ps)
   apply (auto)
  done

lemma aux_ssss:
  assumes "sorted_wrt_a a ps"
  shows "\<forall>p \<in> set (drop n ps). \<forall>p' \<in> set (take n ps). p'!a \<le> p!a"
  using assms
  apply (induction ps)
   apply (auto)
  by (metis (no_types, lifting) append_take_drop_id sorted_wrt.simps(2) sorted_wrt_append)

lemma q:
  "length ps > 0 \<Longrightarrow> n > 0 \<Longrightarrow> last (take n ps) \<in> set ps"
  apply (induction ps)
   apply (auto)
  by (metis in_set_takeD last_in_set list.simps(3) neq0_conv set_ConsD take_eq_Nil)

lemma aux_sssss:
  assumes "sorted_wrt_a a ps" "length ps > 0" "n > 0"
  shows " \<forall>p \<in> set (drop n ps). (last (take n ps))!a \<le> p!a"
  using assms aux_ssss q
  by auto

lemma build'_invar:
  "length ps = 2 ^ k \<Longrightarrow> \<forall>p \<in> set ps. dim p = d \<Longrightarrow> distinct ps \<Longrightarrow> a < d \<Longrightarrow> invar d (build' a d ps)"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "last ?l ! a"

  have A': "?a' < d"
    using "1.prems"(4) by auto

  have A: "\<forall>p \<in> set ?l. dim p = d"
    using "1.prems"(2) in_set_takeD by fastforce
  have B: "distinct ?l"
    using "1.prems" distinct_take aux_d by simp

  have L: "length ps > 1 \<longrightarrow> invar d (build' ?a' d ?l)"
    using 1 aux4 aux5 A B A'
    by (smt length_sort less_numeral_extra(3) mod_by_1 mod_if one_mod_2_pow_eq power_0 sort_wrt_a_def zero_neq_one)

  have C: "\<forall>p \<in> set ?g. dim p = d"
    using "1.prems"(2)
    using in_set_dropD by force
  have D: "distinct ?g"
    using aux_d distinct_drop
    using "1.prems"(3) by blast

  have G: "length ps > 1 \<longrightarrow> invar d (build' ?a' d ?g)"
    using 1 aux6 aux7 C D A'
    by (smt length_sort less_numeral_extra(3) mod_by_1 mod_if one_mod_2_pow_eq power_0 sort_wrt_a_def zero_neq_one)

  have Q: "length ps > 1 \<longrightarrow> build' a d ps = Node a (last ?l ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
     by (meson build'.elims not_less)
      
  have "length ps > 1 \<longrightarrow> (\<forall>p \<in> set ?g. ?disc \<le> p!a)"
    using aux_sssss
    by (metis Euclidean_Division.div_eq_0_iff One_nat_def aux_ss div_2_gt_zero length_greater_0_conv length_sort list.size(3) pos2 sort_wrt_a_def)
  hence GT: "length ps > 1 \<longrightarrow> (\<forall>p \<in> set_kdt (build' ?a' d ?g). ?disc \<le> p!a)"
    by (metis "1.prems"(1) aux7 build'_set length_sort sort_wrt_a_def)

  have LL: "length ps > 1 \<longrightarrow> set ?l = set_kdt (build' ?a' d ?l)"
    using build'_set
    by (smt "1.prems"(1) aux5 length_sort less_numeral_extra(3) mod_by_1 mod_if one_mod_2_pow_eq power_0 sort_wrt_a_def zero_neq_one)

  have "sorted_wrt_a a ?l"
    using aux_s aux_ss by blast
  hence "length ps > 1 \<longrightarrow> (\<forall>p \<in> set ?l. p!a \<le> ?disc)"
    using aux_sss by blast
  hence LT: "length ps > 1 \<longrightarrow> (\<forall>p \<in> set_kdt (build' ?a' d ?l). p!a \<le> ?disc)"
    using Q LL by blast

  have QQ: "length ps > 1 \<longrightarrow> invar d (Node a (last ?l ! a) (build' ?a' d ?l) (build' ?a' d ?g))"
    using L G LT GT 1
    using invar.simps(2) by blast

  show ?case
  proof (cases "length ps \<le> 1")
    case True
then show ?thesis using build'_invar_single "1.prems"
  by (metis le_antisym one_le_numeral one_le_power)
next
  case False
  then show ?thesis using Q QQ
    by (metis not_less)
qed
qed

lemma XX:
  "complete kdt \<Longrightarrow> size_kdt kdt = 2 ^ (height_kdt kdt - 1)"
  apply (induction kdt)
   apply (auto)
  by (metis One_nat_def add_is_0 height_kdt.elims mult_2 one_neq_zero power_eq_if)
  

lemma X:
  assumes "complete kdt1" "complete kdt2" "size_kdt kdt1 = size_kdt kdt2"
  shows "height_kdt kdt1 = height_kdt kdt2"
proof -
  have "2 ^ (height_kdt kdt1 - 1) = 2 ^ (height_kdt kdt2 - 1)"
    using XX assms by simp
  thus ?thesis
    by (smt One_nat_def add_is_0 height_kdt.elims lessI numeral_2_eq_2 one_neq_zero power_eq_if power_inject_exp)
qed

lemma build'_size:
  "length ps = 2 ^ k \<Longrightarrow> size_kdt (build' a d ps) = length ps"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "last ?l ! a"

  have LL: "length ps > 1 \<longrightarrow> length ?l = 2 ^ (k - 1)"
    using "1.prems" aux5 power_0 by fastforce
  hence L: "length ps > 1 \<longrightarrow> size_kdt (build' ?a' d ?l) = length ?l"
    using 1
    by (smt aux4 aux5 less_numeral_extra(3) mod_by_1 mod_if one_mod_2_pow_eq one_neq_zero power_0)

  have GG: "length ps > 1 \<longrightarrow> length ?g = 2 ^ (k - 1)"
    using "1.prems" aux7 power_0 by fastforce
  hence G: "length ps > 1 \<longrightarrow> size_kdt (build' ?a' d ?g) = length ?g"
    using 1
    by (smt aux4 aux5 less_numeral_extra(3) mod_by_1 mod_if one_mod_2_pow_eq one_neq_zero power_0)

  have Q: "length ps > 1 \<longrightarrow> build' a d ps = Node a (last ?l ! a) (build' ?a' d ?l) (build' ?a' d ?g)"
    by (meson build'.elims not_less)

  have Z: "length ps > 1 \<longrightarrow> size_kdt (build' a d ps) = length ps"
    using Q
    by (smt "1.prems" G GG L LL mult_2 nat_neq_iff power_eq_if size_kdt.simps(2))

  show ?case
  proof (cases "length ps \<le> 1")
case True
  then show ?thesis using 1
    by (simp add: antisym)
next
  case False
  then show ?thesis using Z by force
qed
qed

lemma build'_complete:
  "length ps = 2 ^ k \<Longrightarrow> complete (build' a d ps)"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort_wrt_a a ps"
  let ?a' = "(a + 1) mod d"
  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"
  let ?disc = "last ?l ! a"

  have LL: "length ps > 1 \<longrightarrow> length ?l = 2 ^ (k - 1)"
    using "1.prems" aux5 power_0 by fastforce
  hence L: "length ps > 1 \<longrightarrow> complete (build' ?a' d ?l)"
    using 1
    by (metis diff_less one_less_numeral_iff power_0 power_strict_increasing_iff semiring_norm(76) zero_less_one)

  have GG: "length ps > 1 \<longrightarrow> length ?g = 2 ^ (k - 1)"
    using "1.prems" using aux7 by force
  hence G: "length ps > 1 \<longrightarrow> complete (build' ?a' d ?g)"
    using 1
    by (metis diff_less one_less_numeral_iff power_0 power_strict_increasing_iff semiring_norm(76) zero_less_one)

  have "size_kdt (build' ?a' d ?l) = size_kdt (build' ?a' d ?g)"
    using build'_size using LL GG
    by fastforce
  hence H: "length ps > 1 \<longrightarrow> height_kdt (build' ?a' d ?l) = height_kdt (build' ?a' d ?g)"
    using L G X by blast

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using 1 L G H apply (auto)
      by (meson complete.simps(2))
  qed
qed

end