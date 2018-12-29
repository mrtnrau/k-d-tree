theory homework_10
imports
  Complex_Main
begin

text \<open>
  I did take "Functional Data Structures" last semester and verified the range query algorithm
  as final project. Those sections are marked and have already been graded but
  are here for completeness only.

  There is of course some overlap in the initial definitions but I had to change the tree
  by moving the data form the nodes to the leafs and storing the axis in the node to make the
  nearest neighbor algorithm work and adjust the work from last semester accordingly.
  The range query algorithm got simpler but the insertion had to be redone from scratch.
\<close>

text \<open>
  A k-d tree is a space-partitioning data structure for organizing points in a k-dimensional space.
  In principle the k-d tree is a binary tree. The leafs hold the k-dimensional points and the nodes
  contain left and right subtrees as well as a splitting value at a particular axis.
  The tree could also be build with the nodes holding the points and the leafs being empty, but this
  complicates the code and the proofs substantually.
  Every node divides the space into two parts by splitting along a hyperplane.
  Consider a node n with associated splitting axis a with value s.
  All points in the left subtree must have a value at axis a that is less or
  equal than s and all points in the right subtree must have a value at axis a that is
  greater that v.

  e.g.: Consider a 2-d tree.

   0/x-axis:                          N 0 7

   1/y-axis:                N 1 3                N 1 6

   0/x-axis:         N 0 2        N 0 4      (9,6)    N 0 8

                 (2,3) (7, 2)  (4,7) (5,4)         (8,7) (9,9)

  Leaf (4,7) is at its current position because 4 <= 7, 7 > 3 and 4 <= 4.

  More information about k-d trees:

  Bentley, J. L. (1975). "Multidimensional binary search trees used for associative searching".
    https://dl.acm.org/citation.cfm?id=361007

  Friedman, J. (1976). "An Algorithm for Finding Best Matches in Logarithmic Expected Time".
    https://dl.acm.org/citation.cfm?id=892052

  And some slides about construction, range query and nearest neighbor algorithms:
    https://courses.cs.washington.edu/courses/cse373/02au/lectures/lecture22l.pdf
\<close>




text \<open>
  Synonyms for point, axis, dimension and split.
  Definition of the k-d datastructure.
\<close>

type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym split = real

datatype kdt =
  Leaf point
| Node axis split kdt kdt

definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

declare dim_def[simp]




text \<open>
  Abstraction function and invariant.
  Some lemmas for conveniently working with the invariant.
\<close>

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node _ _ l r) = set_kdt l \<union> set_kdt r"

fun size_kdt :: "kdt \<Rightarrow> nat" where
  "size_kdt (Leaf _) = 1"
| "size_kdt (Node _ _ l r) = size_kdt l + size_kdt r"

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar k (Leaf p) \<longleftrightarrow> dim p = k"
| "invar k (Node a s l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> s) \<and> (\<forall>p \<in> set_kdt r. p!a > s) \<and>
    invar k l \<and> invar k r \<and> a < k"

lemma invar_l:
  assumes "invar k (Node a s l r)"
  shows "invar k l"
  using assms by simp

lemma invar_r:
  assumes "invar k (Node a s l r)"
  shows "invar k r"
  using assms by simp

lemma invar_axis_lt_k:
  assumes "invar k (Node a s l r)"
  shows "a < k"
  using assms by simp

lemma invar_dim:
  assumes "invar k kdt"
  shows "\<forall>p \<in> set_kdt kdt. dim p = k"
  using assms by (induction kdt) auto

lemma invar_l_le_a:
  assumes "invar k (Node a s l r)"
  shows "\<forall>p \<in> set_kdt l. p!a \<le> s"
  using assms by simp

lemma invar_r_gt_a:
  assumes "invar k (Node a s l r)"
  shows "\<forall>p \<in> set_kdt r. s < p!a"
  using assms by simp




text \<open>
  New insertion algorithm

  This kdt representation makes insertion quite a bit more difficult but makes verifying
  the nearest neighbor algorithm feasible.
\<close>

fun find_axis' :: "axis \<Rightarrow> point \<Rightarrow> point \<Rightarrow> axis option" where
  "find_axis' 0 p\<^sub>0 p\<^sub>1 = (if p\<^sub>0!0 \<noteq> p\<^sub>1!0 then Some 0 else None)"
| "find_axis' a p\<^sub>0 p\<^sub>1 = (if p\<^sub>0!a \<noteq> p\<^sub>1!a then Some a else find_axis' (a - 1) p\<^sub>0 p\<^sub>1)"

definition find_axis :: "point \<Rightarrow> point \<Rightarrow> axis option" where
  "find_axis p\<^sub>0 p\<^sub>1 = find_axis' (dim p\<^sub>0 - 1) p\<^sub>0 p\<^sub>1"

fun ins :: "point \<Rightarrow> kdt \<Rightarrow> kdt" where
  "ins p (Leaf p') = (
    case find_axis p p' of
      None \<Rightarrow> Leaf p'
    | Some a \<Rightarrow> (
        if p!a < p'!a then
          Node a (p!a) (Leaf p) (Leaf p')
        else
          Node a (p'!a) (Leaf p') (Leaf p)
      )
  )"
| "ins p (Node a s l r) = (
    if p!a \<le> s then
      Node a s (ins p l) r
    else
      Node a s l (ins p r)
  )"




text \<open>Auxiliary lemmas.\<close>

lemma find_axis'_Some_1:
  assumes "find_axis' a p\<^sub>0 p\<^sub>1 = Some a'"
  shows "p\<^sub>0!a' \<noteq> p\<^sub>1!a'"
  using assms
  by (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct) (auto split: if_splits)

lemma find_axis'_Some_2:
  assumes "a < k" "find_axis' a p\<^sub>0 p\<^sub>1 = Some a'"
  shows "a' < k"
  using assms
  by (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct) (auto split: if_splits)

lemma find_axis'_None:
  "(\<forall>i \<le> a. p\<^sub>0!i = p\<^sub>1!i) \<longleftrightarrow> (find_axis' a p\<^sub>0 p\<^sub>1 = None)"
  apply (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct)
  apply (auto)
  using le_SucE by blast

lemma find_axis_Some_1:
  assumes "dim p\<^sub>0 = dim p\<^sub>1" "find_axis p\<^sub>0 p\<^sub>1 = Some a'"
  shows "p\<^sub>0!a' \<noteq> p\<^sub>1!a'"
  using assms find_axis_def find_axis'_Some_1 by metis

lemma find_axis_Some_2:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "find_axis p\<^sub>0 p\<^sub>1 = Some a'"
  shows "a' < k"
  using assms find_axis'_Some_2
  by (metis diff_less find_axis_Some_1 find_axis_def dim_def le_less_linear length_greater_0_conv not_one_le_zero)

lemma find_axis_None:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "(p\<^sub>0 = p\<^sub>1) \<longleftrightarrow> (find_axis p\<^sub>0 p\<^sub>1 = None)"
  unfolding find_axis_def using assms find_axis'_None nth_equalityI
  by (metis One_nat_def Suc_pred dim_def le_simps(2) length_greater_0_conv)




text \<open>Main lemmas about insertion.\<close>

lemma ins_size_eq:
  assumes "invar k kdt" "dim p = k" "p \<in> set_kdt kdt"
  shows "size (ins p kdt) = size kdt"
  using assms
  by (induction kdt) (auto simp add: find_axis_None split: option.splits)

lemma ins_size_1:
  assumes "invar k kdt" "dim p = k" "p \<notin> set_kdt kdt"
  shows "size (ins p kdt) = size kdt + 1"
  using assms
  by (induction kdt) (auto simp add: find_axis_None split: option.splits)

lemma ins_set:
  assumes "invar k kdt" "dim p = k"
  shows "set_kdt (ins p kdt) = {p} \<union> set_kdt kdt"
  using assms find_axis_None 
  by (induction kdt) (auto split: option.splits)

lemma ins_invar:
  assumes "invar k kdt" "dim p = k"
  shows "invar k (ins p kdt)"
  using assms find_axis_Some_1 find_axis_Some_2 ins_set
  apply (induction kdt)
  apply (auto split: option.splits)
  by fastforce




text \<open>
  Verifying nearest neighbor search on the k-d tree.

  Given k-d tree and a point p, which might not be in the tree, find the point p' which is
  closest to p by some metric.

  The chosen metric is the euclidean distance between two points.

  To avoid working with roots I will work with the squared euclidean distance.
\<close>

text \<open>Definitions and lemmas about the squared euclidean distance.\<close>

definition sqed' :: "real \<Rightarrow> real \<Rightarrow> real" where
  "sqed' x y = (x - y) ^ 2"

fun sqed :: "point \<Rightarrow> point \<Rightarrow> real" where
  "sqed [] [] = 0"
| "sqed (x # xs) (y # ys) = sqed' x y + sqed xs ys"
| "sqed _ _ = undefined"

definition min_by_sqed :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "min_by_sqed p\<^sub>0 p\<^sub>1 q = (
    if sqed p\<^sub>0 q \<le> sqed p\<^sub>1 q then p\<^sub>0 else p\<^sub>1
  )"

lemma sqed'_ge_0:
  "sqed' x y \<ge> 0"
  by (simp add: sqed'_def)

lemma sqed'_eq_0[simp]:
  "sqed' x y = 0 \<longleftrightarrow> x = y"
  by (simp add: sqed'_def)

lemma sqed'_com:
  "sqed' x y = sqed' y x"
  by (simp add: sqed'_def power2_commute)

lemma inequality:
  assumes "(x::real) \<le> 0" "y \<le> 0"
  shows "x\<^sup>2 + y\<^sup>2 \<le> (x + y)\<^sup>2"
proof -
  have "x\<^sup>2 + y\<^sup>2 \<le> x\<^sup>2 + 2 * x * y + y\<^sup>2"
    using assms by (simp add: zero_le_mult_iff)
  also have "... = (x + y)\<^sup>2"
    by algebra
  finally show ?thesis .
qed

lemma sqed'_split:
  assumes "x \<le> s" "s \<le> y"
  shows "sqed' x y \<ge> sqed' x s + sqed' s y"
  unfolding sqed'_def using inequality assms by smt

lemma sqed_ge_0:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> 0"
  using assms 
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  assumes "p\<^sub>0 = p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = 0"
  using assms 
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_eq_0_rev:
  assumes "dim p\<^sub>0 = dim p\<^sub>1" "sqed p\<^sub>0 p\<^sub>1 = 0"
  shows "p\<^sub>0 = p\<^sub>1"
  using assms
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: add_nonneg_eq_0_iff sqed'_ge_0 sqed_ge_0)

lemma sqed_com:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  using assms 
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)




text\<open>The nearest neighbor algorithm.\<close>

fun nearest_neighbor :: "dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor _ _ (Leaf p) = p"
| "nearest_neighbor k p (Node a s l r) = (
    if p!a \<le> s then
      let candidate = nearest_neighbor k p l in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor k p r in
        min_by_sqed candidate candidate' p
    else
      let candidate = nearest_neighbor k p r in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor k p l in
        min_by_sqed candidate candidate' p
  )"




text \<open>First part of main theorem.\<close>

lemma nearest_neighbor_in_kdt:
  "nearest_neighbor k p kdt \<in> set_kdt kdt"
  by (induction kdt) (auto simp add: Let_def min_by_sqed_def)




text \<open>Second part of main theorem.\<close>

text \<open>Auxiliary lemmas.\<close>

text \<open>
  Some intuition about this step:

  Scenario A:
  We are searching for the nearest neighbor of point p and have found candidate c at axis a.
  Since sqed c p <= sqed' s (p!a) we do not need to check the right side.

                                s
          c                     |
                                |
               p                |
                                |
                                |  q
                                |


  Scenario B:
  We are searching for the nearest neighbor of point p and have found candidate c at axis a.
  Since sqed c p > sqed' s (p!a) we do need to check the right side.

                                s
          c                     |
                                |
                          p     |  q'
                                |
                                |  q
                                |

  The minimize_sqed lemma moves q to q' by setting all coordinates of q' (except the current axis a)
  to the coordinates of p and minimizes the distance between p and q'.
\<close>

lemma minimize_sqed:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "a < k"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a)"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a k rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (smt sqed'_ge_0)

lemma cutoff_r:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "p!a \<le> s" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  (* The distance between p and q is greater or equal the minimized distance between p and q' *)
  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,2) invar_axis_lt_k invar_dim invar_r by blast
  (* Hence it is greater or equal to the distance from p to s + the distance from s to q' *)
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,3) dim_def nth_list_update_eq invar_axis_lt_k invar_r_gt_a sqed'_split)
  (* Hence it is greater or equal to the distance from p to c since sqed' s (q!a) \<ge> 0 *)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

lemma cutoff_l:
  assumes "invar k (Node a s l r)" "dim p = k"
  assumes "s \<le> p!a" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed invar_dim invar_l invar_axis_lt_k assms(1,2) by blast
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,3) dim_def invar_axis_lt_k invar_l_le_a nth_list_update_eq sqed'_com sqed'_split)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed




text \<open>The main proof and the final theorem.\<close>

lemma nearest_neighbor_minimal:
  assumes "invar k kdt" "dim p = k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor k p kdt) p \<le> sqed q p"
  using assms
proof (induction kdt)
  case (Leaf p)
  thus ?case by simp
next
  case (Node a s l r)
  let ?candidate_l = "nearest_neighbor k p l"
  let ?candidate_r = "nearest_neighbor k p r"

  have IHL: "\<forall>q \<in> set_kdt l. sqed ?candidate_l p \<le> sqed q p"
    using Node.IH(1) Node.prems(1) invar_axis_lt_k assms(2) by auto
  have IHR: "\<forall>q \<in> set_kdt r. sqed ?candidate_r p \<le> sqed q p"
    using Node.IH(2) Node.prems(1) invar_axis_lt_k assms(2) by auto

  consider (A) "p!a \<le> s \<and> sqed p ?candidate_l \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>sqed p ?candidate_l \<le> sqed' s (p!a)"
         | (C) "s < p!a \<and> sqed p ?candidate_r \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>sqed p ?candidate_r \<le> sqed' s (p!a)"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed p ?candidate_l \<le> sqed p q"
      using Node.prems(1) assms(2) cutoff_r invar_axis_lt_k invar_l nearest_neighbor_in_kdt by blast
    thus ?thesis using A Node.prems IHL
      apply (auto)
      by (metis assms(2) invar_dim nearest_neighbor_in_kdt sqed_com)
  next
    case B
    thus ?thesis using Node.prems IHL IHR
      by (auto simp add: min_by_sqed_def Let_def)
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed p ?candidate_r \<le> sqed p q"
      using Node.prems(1) assms(2) cutoff_l invar_r invar_axis_lt_k nearest_neighbor_in_kdt by smt
    thus ?thesis using C Node.prems IHR
      apply (auto)
      by (metis (mono_tags, lifting) assms(2) invar_dim nearest_neighbor_in_kdt sqed_com)
  next
    case D
    thus ?thesis using Node.prems IHL IHR
      by (auto simp add: min_by_sqed_def Let_def)
  qed
qed

theorem nearest_neighbor:
  assumes "invar k kdt" "dim p = k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor k p kdt) p \<le> sqed q p) \<and> nearest_neighbor k p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor_in_kdt nearest_neighbor_minimal invar_axis_lt_k by simp

corollary
  assumes "invar k kdt" "p \<in> set_kdt kdt"
  shows "nearest_neighbor k p kdt = p"
  using assms by (smt invar_dim nearest_neighbor sqed_eq_0 sqed_eq_0_rev sqed_ge_0)




(* *)

fun merge :: "point \<Rightarrow> point list \<Rightarrow> point list \<Rightarrow> point list" where
  "merge _ [] [] = []"
| "merge _ [] ys = ys"
| "merge _ xs [] = xs"
| "merge p (x # xs) (y # ys) = (
    if sqed x p \<le> sqed y p then
      x # merge p xs (y # ys)
    else
      y # merge p (x # xs) ys
  )"

fun m_nearest_neighbors :: "nat \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "m_nearest_neighbors _ _ _ (Leaf p) = [p]"
| "m_nearest_neighbors m k p (Node a s l r) = (
    if p!a \<le> s then
      let candidates = m_nearest_neighbors m k p l in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        let candidates' = m_nearest_neighbors m k p r in
        take m (merge p candidates candidates')
    else
      let candidates = m_nearest_neighbors m k p r in
      if length candidates = m \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        let candidates' = m_nearest_neighbors m k p l in
        take m (merge p candidates candidates')
  )"




lemma sorted_wrt_take:
  assumes "sorted_wrt f xs"
  shows "sorted_wrt f (take n xs)"
  using assms
  apply (induction xs arbitrary: n)
  apply (auto)
  by (metis append_take_drop_id sorted_wrt.simps(2) sorted_wrt_append)

lemma distinct_kdt:
  assumes "invar k kdt" "kdt = Node a s l r"
  shows "set_kdt l \<inter> set_kdt r = {}"
  using assms
  by (induction kdt) (auto simp add: leD)

lemma merge_union:
  "set (merge p ps\<^sub>0 ps\<^sub>1) = set ps\<^sub>0 \<union> set ps\<^sub>1"
  by (induction p ps\<^sub>0 ps\<^sub>1 rule: merge.induct) auto

lemma merge_length:
  "length (merge p ps\<^sub>0 ps\<^sub>1) = length ps\<^sub>0 + length ps\<^sub>1"
  by (induction p ps\<^sub>0 ps\<^sub>1 rule: merge.induct) auto

lemma merge_distinct:
  assumes "distinct ps\<^sub>0" "distinct ps\<^sub>1" "set ps\<^sub>0 \<inter> set ps\<^sub>1 = {}"
  shows "distinct (merge p ps\<^sub>0 ps\<^sub>1)"
  using assms
  by (induction p ps\<^sub>0 ps\<^sub>1 rule: merge.induct) (auto simp add: merge_union)

lemma merge_sorted_wrt_sqed_p:
  assumes "sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p) ps\<^sub>0" "sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p) ps\<^sub>1"
  shows "sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p) (merge p ps\<^sub>0 ps\<^sub>1)"
  using assms
  by (induction p ps\<^sub>0 ps\<^sub>1 rule: merge.induct) (auto simp add: merge_union)

theorem m_nearest_neighbors_min_m_size_kdt:
  assumes "m > 0"
  shows "length (m_nearest_neighbors m k p kdt) = min m (size_kdt kdt)"
  using assms
  by (induction kdt) (auto simp add: merge_length Let_def)

theorem m_nearest_neighbors_sorted_wrt_sqed_p:
  "sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p) (m_nearest_neighbors m k p kdt)"
  by (induction kdt) (auto simp add: merge_sorted_wrt_sqed_p sorted_wrt_take Let_def)

theorem m_nearest_neighbors_in_kdt:
  "set (m_nearest_neighbors m k p kdt) \<subseteq> set_kdt kdt"
  apply (induction kdt)
  apply (auto)
  by (smt UnE in_set_takeD merge_union subsetCE)+

theorem m_nearest_neighbors_distinct:
  assumes "invar k kdt" "dim p = k"
  shows "distinct (m_nearest_neighbors m k p kdt)"
  using assms
  apply (induction kdt)
  apply (auto simp add: Let_def)
  by (smt merge_distinct distinct_kdt m_nearest_neighbors_in_kdt Int_emptyI distinct_take subsetCE)+

lemma m_nearest_neighbors_optimum':
  assumes "invar k kdt" "dim p = k" "m_nearest_neighbors m k p kdt = ns"
  shows "\<forall>q \<in> set_kdt kdt. q \<notin> set ns \<longrightarrow> sqed (last ns) p \<le> sqed q p"
  using assms
  sorry

lemma aux:
  assumes "sorted_wrt f (xs @ [x])"
  shows "\<forall>x' \<in> set xs. f x' x"
  using assms by (induction xs) auto

theorem m_nearest_neighbors_optimum:
  assumes "invar k kdt" "dim p = k" "m_nearest_neighbors m k p kdt = ns"
  shows "\<forall>n \<in> set ns. (\<forall>q \<in> set_kdt kdt. q \<notin> set ns \<longrightarrow> sqed n p \<le> sqed q p)"
proof standard
  fix n
  assume N: "n \<in> set ns"
  show "\<forall>q \<in> set_kdt kdt. q \<notin> set ns \<longrightarrow> sqed n p \<le> sqed q p"
  proof standard
    fix q
    assume "q \<in> set_kdt kdt"

    hence A: "q \<notin> set ns \<longrightarrow> sqed (last ns) p \<le> sqed q p"
      using assms(1,2,3) m_nearest_neighbors_optimum' by blast

    have B: "\<forall>n' \<in> set ns. sqed n' p \<le> sqed (last ns) p"
      using m_nearest_neighbors_sorted_wrt_sqed_p[of p m k kdt] aux[of "(\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p)" "butlast ns" "last ns"]
      by (smt append_butlast_last_id assms(3) empty_iff list.set(1) rotate1.simps(2) set_ConsD set_rotate1)

    show "q \<notin> set ns \<longrightarrow> sqed n p \<le> sqed q p" using N A B by fastforce
  qed
qed




(* FROM HERE ON LAST SEMESTER *)

text \<open>
  Verifying k-dimensional queries on the k-d tree.

  Given two k-dimensional points p\<^sub>0 and p\<^sub>1 which bound the search space, the query should return
  only the points which satisfy the following criteria:

  For every point p in the resulting set:
    For every axis a \<in> [0, k-1]:
      min (p\<^sub>0!a) (p\<^sub>1!a) <= p!a and p!a <= max (p\<^sub>0!a) (p\<^sub>1!a)

  For example: In a 2-d tree a query corresponds to selecting all the points in
  the rectangle which has p\<^sub>0 and p\<^sub>1 as its defining edges.
\<close>

text \<open>
  Simplifying the problem:

  Assume that the two given points p\<^sub>0 and p\<^sub>1 which define the bounding box are the left lower
  and the right upper point.

  For every point p in the resulting set:
    For every axis a \<in> [0, k-1]:
      p\<^sub>0!a <= p\<^sub>1!a
\<close>

text\<open>The query function and auxiliary definitions:\<close>

definition is_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "is_bounding_box k p\<^sub>0 p\<^sub>1 \<longleftrightarrow> dim p\<^sub>0 = k \<and> dim p\<^sub>1 = k \<and> (\<forall>i < k. p\<^sub>0!i \<le> p\<^sub>1!i)"

definition point_in_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "point_in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. p\<^sub>0!i \<le> p!i \<and> p!i \<le> p\<^sub>1!i)"

fun query_area' :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area' k p\<^sub>0 p\<^sub>1 (Leaf p) = (
    if point_in_bounding_box k p p\<^sub>0 p\<^sub>1 then {p} else {}
  )"
| "query_area' k p\<^sub>0 p\<^sub>1 (Node a s l r) = (
    if s < p\<^sub>0!a then
      query_area' k p\<^sub>0 p\<^sub>1 r
    else if p\<^sub>1!a \<le> s then
      query_area' k p\<^sub>0 p\<^sub>1 l
    else
      query_area' k p\<^sub>0 p\<^sub>1 l \<union> query_area' k p\<^sub>0 p\<^sub>1 r
  )"




text \<open>Auxiliary lemmas:\<close>

lemma l_pibb_empty:
  assumes "invar k (Node a s l r)" "s < p\<^sub>0!a"
  shows "{ p \<in> set_kdt l. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt l. p!a < p\<^sub>0!a"
    using invar_l_le_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt l. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_k by blast
  hence "\<forall>p \<in> set_kdt l. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
    using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

lemma r_pibb_empty:
  assumes "invar k (Node a s l r)" "p\<^sub>1!a \<le> s"
  shows "{ p \<in> set_kdt r. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt r. p\<^sub>1!a < p!a"
    using invar_r_gt_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt r. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_k by blast
  hence "\<forall>p \<in> set_kdt r. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
   using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed




text \<open>The simplified main theorem:\<close>

theorem query_area':
  assumes "invar k kdt"
  shows "query_area' k p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms l_pibb_empty r_pibb_empty
  by (induction kdt) auto




text \<open>
  Un-simplifying the problem:

  Given two arbitrary points p\<^sub>0 and p\<^sub>1 which only satisfy the dimensionality property,
  does the query function work?

  Hide the is_bounding_box abstraction.
\<close>

text \<open>Auxiliary functions and the final query function:\<close>

fun min_max :: "real * real \<Rightarrow> real * real" where
  "min_max (a, b) = (min a b, max a b)"

definition to_bounding_box :: "point \<Rightarrow> point \<Rightarrow> point * point" where
  "to_bounding_box p\<^sub>0 p\<^sub>1 = (let ivs = map min_max (zip p\<^sub>0 p\<^sub>1) in (map fst ivs, map snd ivs))"

definition query_area :: "point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area q\<^sub>0 q\<^sub>1 kdt = (let (p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1 in query_area' (dim q\<^sub>0) p\<^sub>0 p\<^sub>1 kdt)"




text \<open>Auxiliary lemmas and the final theorem:\<close>

lemma tbbibb:
  assumes "k = dim q\<^sub>0" "k = dim q\<^sub>1" "(p\<^sub>0 ,p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "is_bounding_box k p\<^sub>0 p\<^sub>1"
  using assms by (auto simp add: to_bounding_box_def is_bounding_box_def)

lemma pibb:
  assumes "k = dim q\<^sub>0" "k = dim q\<^sub>1" "(p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "point_in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i))"
  using assms by (auto simp add: min_def max_def to_bounding_box_def point_in_bounding_box_def)

theorem query_area:
  assumes "invar k kdt" "k = dim q\<^sub>0" "k = dim q\<^sub>1"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> x!i \<and> x!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i) }"
  using assms pibb tbbibb query_area' by (auto simp add: query_area_def)

corollary
  assumes "invar k kdt" "k = dim q\<^sub>0" "k = dim q\<^sub>1"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = query_area q\<^sub>1 q\<^sub>0 kdt"
  using assms query_area by auto

corollary
  assumes "invar k kdt" "k = dim q\<^sub>0" "k = dim q\<^sub>1" "p \<in> set_kdt kdt" "\<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i)"
  shows "p \<in> query_area q\<^sub>0 q\<^sub>1 kdt"
  using assms query_area by blast

corollary
  assumes "invar k kdt" "k = dim q\<^sub>0" "q\<^sub>0 = q\<^sub>1" "q\<^sub>0 \<in> set_kdt kdt"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = { q\<^sub>0 }"
proof -
  have QA: "query_area q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < k. q\<^sub>0!i = x!i }"
    using query_area assms(1,2,3) by auto

  have A: "\<forall>p \<in> query_area q\<^sub>0 q\<^sub>1 kdt. dim p = k"
    using assms(1) QA invar_dim by blast
  have B: "q\<^sub>0 \<in> query_area q\<^sub>0 q\<^sub>1 kdt"
    using assms(4) QA by blast
  have C: "\<forall>p \<noteq> q\<^sub>0. dim p = k \<longrightarrow> (\<exists>i < k. q\<^sub>0!i \<noteq> p!i)"
    using assms(2) nth_equalityI by fastforce

  show ?thesis using QA A B C by blast
qed

end
