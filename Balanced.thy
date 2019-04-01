theory Balanced
imports
  Complex_Main
begin

type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym disc = point

definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

declare dim_def[simp]

datatype kdt =
  Leaf point
| Node axis disc kdt kdt



datatype ord = LT | EQ | GT

fun cmp' :: "axis \<Rightarrow> point \<Rightarrow> point \<Rightarrow> ord" where
  "cmp' 0 p q = (
    if p!0 < q!0 then LT
    else if p!0 > q!0 then GT
    else EQ
  )"
| "cmp' a p q = (
    if p!a < q!a then LT
    else if p!a > q!a then GT
    else cmp' (a - 1) p q
  )"

fun cmp :: "axis \<Rightarrow> point \<Rightarrow> point \<Rightarrow> ord" where
  "cmp a p q = (
    if p!a < q!a then LT
    else if p!a > q!a then GT
    else cmp' (dim p - 1) p q
  )"

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node _ _ l r) = set_kdt l \<union> set_kdt r"

fun size_kdt :: "kdt \<Rightarrow> nat" where
  "size_kdt (Leaf _) = 1"
| "size_kdt (Node _ _ l r) = size_kdt l + size_kdt r"

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar d (Leaf p) \<longleftrightarrow> dim p = d"
| "invar d (Node a disc l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. cmp a p disc = LT \<or> cmp a p disc = EQ) \<and> (\<forall>p \<in> set_kdt r. cmp a p disc = GT) \<and>
    invar d l \<and> invar d r \<and> a < d"

lemma cmp'_EQ:
  "(\<forall>i \<le> a. p!i = q!i) \<longleftrightarrow> cmp' a p q = EQ"
  by (induction a) (auto elim: le_SucE)

lemma cmp_EQ:
  "dim p = dim q \<Longrightarrow> p = q \<longleftrightarrow> cmp a p q = EQ"
  apply (induction a)
  apply (auto)
  by (metis Suc_pred cmp'_EQ length_greater_0_conv less_Suc_eq_le nth_equalityI)+

lemma cmp'_rev:
  "cmp' a p q = GT \<Longrightarrow> cmp' a q p = LT"
  apply (induction a)
  apply (auto split: if_splits)
  done

lemma cmp'_trans:
  "dim x = d \<Longrightarrow> dim y = d \<Longrightarrow> dim z = d \<Longrightarrow> cmp' a x y = LT \<Longrightarrow> cmp' a y z = LT \<Longrightarrow> cmp' a x z = LT"
  apply (induction a)
  apply (auto split: if_splits)
  done
  
fun sorted :: "axis \<Rightarrow> point list \<Rightarrow> bool" where
  "sorted _ [] = True" 
| "sorted a (p # ps) = (
    (\<forall>q \<in> set ps. cmp a p q = LT \<or> cmp a p q = EQ) \<and> sorted a ps
  )"

fun insort :: "axis \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point list" where
  "insort _ p [] = [p]"
| "insort a p (q # ps) = (
    if cmp a p q = LT then p # q # ps
    else if cmp a p q = GT then q # insort a p ps
    else p # q # ps
  )"

definition sort :: "axis \<Rightarrow> point list \<Rightarrow> point list" where
  "sort a ps = foldr (insort a) ps []"

lemma insort_length:
  "length (insort a p ps) = length ps + 1"
  by (induction ps) auto

lemma sort_length:
  "length (sort a ps) = length ps"
  unfolding sort_def
  by (induction ps) (auto simp add: insort_length)

lemma insort_set:
  "set (insort a p ps) = {p} \<union> set ps"
  by (induction ps) auto

lemma sort_set:
  "set (sort a ps) = set ps"
  unfolding sort_def
  by (induction ps) (auto simp add: insort_set)

lemma insort_sorted:
  "dim p = d \<Longrightarrow> \<forall>p \<in> set ps. dim p = d \<Longrightarrow> sorted a ps \<Longrightarrow> sorted a (insort a p ps)"
  apply (induction ps arbitrary: a)
  apply (auto simp add: insort_set split: if_splits)
  using cmp'_rev apply blast
  apply (smt dim_def Suc_pred cmp'_EQ cmp'_trans length_greater_0_conv lessI less_Suc_eq_le nth_equalityI)
  using ord.exhaust apply blast
  by (smt Suc_pred cmp'_EQ length_greater_0_conv less_Suc_eq_le nth_equalityI ord.exhaust)

lemma sort_sorted:
  "\<forall>p \<in> set ps. dim p = d \<Longrightarrow> sorted a (sort a ps)"
  unfolding sort_def using insort_sorted sort_set sort_def
  apply (induction ps)
  apply (auto)
  done

definition split :: "axis \<Rightarrow> point list \<Rightarrow> point list * point list" where
  "split a ps = (
    let sps = sort a ps in
    let n = length ps div 2 in
    (take n sps, drop n sps)
  )"

lemma split_length:
  "split a ps = (l, g) \<Longrightarrow> length ps = length l + length g"
  unfolding split_def by (auto simp add: Let_def sort_length)

lemma aux:
  "set (take n xs) \<union> set (drop n xs) = set xs"
  by (metis append_take_drop_id set_append)

lemma split_set:
  "split a ps = (l, g) \<Longrightarrow> set ps = set l \<union> set g"
  unfolding split_def using sort_set aux[of "length ps div 2" "sort a ps"] apply (auto simp add: Let_def)
  done

lemma split_length_g_l:
  "split a ps = (l, g) \<Longrightarrow> length g \<ge> length l"
  unfolding split_def using sort_length by (auto simp add: Let_def)

lemma split_length_diff:
  "split a ps = (l, g) \<Longrightarrow> length g - length l \<le> 1"
  unfolding split_def using sort_length by (auto simp add: Let_def)

lemma split_length_eq:
  "k > 0 \<Longrightarrow> length ps = 2 ^ k \<Longrightarrow> split a ps = (l, g) \<Longrightarrow> length l = length g"
  unfolding split_def using sort_length apply (auto simp add: Let_def min_def) sorry

lemma aux2:
  "split a ps = (l, g) \<Longrightarrow> sort a ps = l @ g"
  unfolding split_def by (auto simp add: Let_def)

function (sequential) build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a d ps = (
    if length ps \<le> 1 then
      Leaf (hd ps) 
    else
      let sps = sort a ps in
      let n = length sps div 2 in
      let l = take n sps in
      let g = drop n sps in
      let a' = (a + 1) mod d in
      Node a (last l) (build' a' d l) (build' a' d g)
  )"
        apply pat_completeness
       apply auto
  done
termination
  sorry


lemma aux4: 
  "length xs = 2 ^ k \<Longrightarrow> length (take (length xs div 2) xs) < length xs"
  by (metis Euclidean_Division.div_eq_0_iff div_greater_zero_iff div_less_dividend length_take min_def nat_less_le one_less_numeral_iff pos2 semiring_norm(76) zero_less_power)

lemma aux5:
  "length xs = 2 ^ k \<Longrightarrow> k > 0 \<Longrightarrow> length (take (length xs div 2) xs) = 2 ^ (k - 1)"
  by (metis aux4 length_take min_def nat_neq_iff nat_zero_less_power_iff nonzero_mult_div_cancel_right power_minus_mult zero_power2)

lemma aux6: 
  "length xs = 2 ^ k \<Longrightarrow> k > 0 \<Longrightarrow> length (drop (length xs div 2) xs) < length xs"
  by (metis Suc_leI diff_less div_2_gt_zero length_drop n_not_Suc_n nat_less_le nat_power_eq_Suc_0_iff numeral_2_eq_2 pos2 zero_less_power)

lemma aux7:
  "length xs = 2 ^ k \<Longrightarrow> length (drop (length xs div 2) xs) = 2 ^ (k - 1)"
  by (smt Euclidean_Division.div_eq_0_iff One_nat_def Suc_eq_plus1 Suc_leI add_diff_cancel_right' diff_Suc_Suc diff_is_0_eq' gr0I length_drop mult_2 nonzero_mult_div_cancel_right one_less_numeral_iff power.simps(1) power_commutes power_minus_mult rel_simps(76) semiring_norm(76))

lemma build'_set_single:
  "length ps = 1 \<Longrightarrow> set ps = set_kdt (build' a d ps)"
  apply (auto)
  apply (metis length_Suc_conv length_pos_if_in_set less_numeral_extra(3) list.sel(1) list.sel(3) list.set_cases)
  by (metis length_greater_0_conv less_Suc0 list.set_sel(1))

lemma build'_set:
  "length ps = 2 ^ k \<Longrightarrow> set ps = set_kdt (build' a d ps)"
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)

  let ?sps = "sort a ps"
  let ?a' = "(a + 1) mod d"

  let ?l = "take (length ?sps div 2) ?sps"
  let ?g = "drop (length ?sps div 2) ?sps"

  have L: "length ps > 1 \<longrightarrow> set ?l = set_kdt (build' ?a' d ?l)"
    using 1 sort_length aux4 aux5
    by (metis one_less_numeral_iff power_0 power_strict_increasing_iff semiring_norm(76))

  have G: "length ps > 1 \<longrightarrow> set ?g = set_kdt (build' ?a' d ?g)"
    using 1 sort_length aux6 aux7
    by (metis length_drop one_less_numeral_iff power_0 power_strict_increasing_iff semiring_norm(76))

  have "length ps > 1 \<longrightarrow> build' a d ps = Node a (last ?l) (build' ?a' d ?l) (build' ?a' d ?g)"
     by (meson build'.elims not_less)
  hence X: "length ps > 1 \<longrightarrow> set_kdt (build' a d ps) = set_kdt (build' ?a' d ?l) \<union> set_kdt (build' ?a' d ?g)"
    by simp
  have Y: "length ps > 1 \<longrightarrow> set ps = set ?l \<union> set ?g"
    by (simp add: aux sort_set)

  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then show ?thesis using 1 build'_set_single
      by (simp add: le_eq_less_or_eq)
  next
    case False
    then show ?thesis using L G X Y by simp
  qed
qed

end