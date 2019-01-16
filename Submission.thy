theory Submission
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
  The range query algorithm got simpler and could be easily adapted to the new tree
  but the insertion had to be redone from scratch.
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
  Abstraction function, size measure and invariant.
  Some lemmas for conveniently working with the invariant.
\<close>

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node _ _ l r) = set_kdt l \<union> set_kdt r"

fun size_kdt :: "kdt \<Rightarrow> nat" where
  "size_kdt (Leaf _) = 1"
| "size_kdt (Node _ _ l r) = size_kdt l + size_kdt r"

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar d (Leaf p) \<longleftrightarrow> dim p = d"
| "invar d (Node a s l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> s) \<and> (\<forall>p \<in> set_kdt r. p!a > s) \<and>
    invar d l \<and> invar d r \<and> a < d"

lemma invar_l:
  "invar d (Node a s l r) \<Longrightarrow> invar d l"
  by simp

lemma invar_r:
  "invar d (Node a s l r) \<Longrightarrow> invar d r"
  by simp

lemma invar_axis_lt_d:
  "invar d (Node a s l r) \<Longrightarrow> a < d"
  by simp

lemma invar_dim:
  "invar d kdt \<Longrightarrow> \<forall>p \<in> set_kdt kdt. dim p = d"
  by (induction kdt) auto

lemma invar_l_le_a:
  "invar d (Node a s l r) \<Longrightarrow> \<forall>p \<in> set_kdt l. p!a \<le> s"
  by simp

lemma invar_r_gt_a:
  "invar d (Node a s l r) \<Longrightarrow> \<forall>p \<in> set_kdt r. s < p!a"
  by simp

lemma invar_distinct:
  "invar d kdt \<Longrightarrow> kdt = Node a s l r \<Longrightarrow> set_kdt l \<inter> set_kdt r = {}"
  by fastforce

lemma invar_set:
  "set_kdt (Node a s l r) = set_kdt l \<union> set_kdt r"
  by simp




text \<open>
  New insertion algorithm

  This kdt representation makes insertion quite a bit more difficult but makes verifying
  the nearest neighbor algorithm possible.
\<close>

(* finds an axis a where the values of p\<^sub>0!a and p\<^sub>1!a differ or returns None *)
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
  "find_axis' a p\<^sub>0 p\<^sub>1 = Some a' \<Longrightarrow> p\<^sub>0!a' \<noteq> p\<^sub>1!a'"
  by (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct) (auto split: if_splits)

lemma find_axis'_Some_2:
  "a < d \<Longrightarrow> find_axis' a p\<^sub>0 p\<^sub>1 = Some a' \<Longrightarrow> a' < d"
  by (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct) (auto split: if_splits)

lemma find_axis'_None:
  "(\<forall>i \<le> a. p\<^sub>0!i = p\<^sub>1!i) \<longleftrightarrow> (find_axis' a p\<^sub>0 p\<^sub>1 = None)"
  by (induction a p\<^sub>0 p\<^sub>1 rule: find_axis'.induct) (auto elim: le_SucE)

lemma find_axis_Some_1:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> find_axis p\<^sub>0 p\<^sub>1 = Some a' \<Longrightarrow> p\<^sub>0!a' \<noteq> p\<^sub>1!a'"
  using find_axis_def find_axis'_Some_1 by metis

lemma find_axis_Some_2:
  "dim p\<^sub>0 = d \<Longrightarrow> dim p\<^sub>1 = d \<Longrightarrow> find_axis p\<^sub>0 p\<^sub>1 = Some a' \<Longrightarrow> a' < d"
  using find_axis_def find_axis_Some_1 find_axis'_Some_2
  by (metis dim_def diff_less length_greater_0_conv less_one)

lemma find_axis_None:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> (p\<^sub>0 = p\<^sub>1) \<longleftrightarrow> (find_axis p\<^sub>0 p\<^sub>1 = None)"
  using find_axis_def find_axis'_None nth_equalityI sledgehammer
  by (metis One_nat_def dim_def Suc_pred length_greater_0_conv less_Suc_eq_le)




text \<open>Main lemmas about insertion.\<close>

lemma ins_size_eq:
  "invar d kdt \<Longrightarrow> dim p = d \<Longrightarrow> p \<in> set_kdt kdt \<Longrightarrow> size (ins p kdt) = size kdt"
  by (induction kdt) (auto simp add: find_axis_None split: option.splits)

lemma ins_size_1:
  "invar d kdt \<Longrightarrow> dim p = d \<Longrightarrow> p \<notin> set_kdt kdt \<Longrightarrow> size (ins p kdt) = size kdt + 1"
  by (induction kdt) (auto simp add: find_axis_None split: option.splits)

lemma ins_set:
  "invar d kdt \<Longrightarrow> dim p = d \<Longrightarrow> set_kdt (ins p kdt) = {p} \<union> set_kdt kdt"
  by (induction kdt) (auto simp add: find_axis_None split: option.splits)

lemma ins_invar:
  "invar d kdt \<Longrightarrow> dim p = d \<Longrightarrow> invar d (ins p kdt)"
  using find_axis_Some_1 find_axis_Some_2 ins_set
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
  "x \<le> s \<Longrightarrow> s \<le> y \<Longrightarrow> sqed' x y \<ge> sqed' x s + sqed' s y"
  using sqed'_def inequality by smt

lemma sqed_ge_0:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 \<ge> 0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  "p\<^sub>0 = p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_eq_0_rev:
  "dim p\<^sub>0 = dim p\<^sub>1 \<Longrightarrow> sqed p\<^sub>0 p\<^sub>1 = 0 \<Longrightarrow> p\<^sub>0 = p\<^sub>1"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: add_nonneg_eq_0_iff sqed'_ge_0 sqed_ge_0)

lemma sqed_com:
  "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)




text\<open>The nearest neighbor algorithm.\<close>

fun nearest_neighbor :: "point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor _ (Leaf p) = p"
| "nearest_neighbor p (Node a s l r) = (
    if p!a \<le> s then
      let candidate = nearest_neighbor p l in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor p r in
        min_by_sqed candidate candidate' p
    else
      let candidate = nearest_neighbor p r in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor p l in
        min_by_sqed candidate candidate' p
  )"




text \<open>First part of main theorem.\<close>

lemma nearest_neighbor_in_kdt:
  "nearest_neighbor p kdt \<in> set_kdt kdt"
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
  assumes "dim p\<^sub>0 = d" "dim p\<^sub>1 = d" "a < d"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a)"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a d rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (smt sqed'_ge_0)

lemma cutoff_r:
  assumes "invar d (Node a s l r)" "dim p = d"
  assumes "p!a \<le> s" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  (* The distance between p and q is greater or equal the minimized distance between p and q' *)
  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,2) invar_axis_lt_d invar_dim invar_r by blast
  (* Hence it is greater or equal to the distance from p to s + the distance from s to q' *)
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,3) dim_def nth_list_update_eq invar_axis_lt_d invar_r_gt_a sqed'_split)
  (* Hence it is greater or equal to the distance from p to c since sqed' s (q!a) \<ge> 0 *)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

lemma cutoff_l:
  assumes "invar d (Node a s l r)" "dim p = d"
  assumes "s \<le> p!a" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed invar_dim invar_l invar_axis_lt_d assms(1,2) by blast
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,3) dim_def invar_axis_lt_d invar_l_le_a nth_list_update_eq sqed'_com sqed'_split)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(4) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed




text \<open>The main theorem.\<close>

lemma nearest_neighbor_minimal:
  assumes "invar d kdt" "dim p = d"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p"
  using assms
proof (induction kdt)
  case (Leaf p)
  thus ?case by simp
next
  case (Node a s l r)

  let ?cl = "nearest_neighbor p l"
  let ?cr = "nearest_neighbor p r"

  have IHL: "\<forall>q \<in> set_kdt l. sqed ?cl p \<le> sqed q p"
    using Node.IH(1) Node.prems(1,2) invar_axis_lt_d by auto
  have IHR: "\<forall>q \<in> set_kdt r. sqed ?cr p \<le> sqed q p"
    using Node.IH(2) Node.prems(1,2) invar_axis_lt_d by auto

  consider (A) "p!a \<le> s \<and> sqed p ?cl \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>sqed p ?cl \<le> sqed' s (p!a)"
         | (C) "s < p!a \<and> sqed p ?cr \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>sqed p ?cr \<le> sqed' s (p!a)"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed p ?cl \<le> sqed p q"
      using Node.prems(1,2) cutoff_r invar_axis_lt_d invar_l nearest_neighbor_in_kdt by blast
    thus ?thesis using A Node.prems IHL by (auto simp add: sqed_com)
  next
    case B
    thus ?thesis using Node.prems IHL IHR
      by (auto simp add: min_by_sqed_def Let_def)
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed p ?cr \<le> sqed p q"
      using Node.prems(1,2) cutoff_l invar_r invar_axis_lt_d nearest_neighbor_in_kdt by smt
    thus ?thesis using C Node.prems IHR by (auto simp add: sqed_com)
  next
    case D
    thus ?thesis using Node.prems IHL IHR
      by (auto simp add: min_by_sqed_def Let_def)
  qed
qed

theorem nearest_neighbor:
  assumes "invar d kdt" "dim p = d"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p) \<and> nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor_in_kdt nearest_neighbor_minimal invar_axis_lt_d by simp

corollary
  assumes "invar d kdt" "p \<in> set_kdt kdt"
  shows "nearest_neighbor p kdt = p"
  using assms by (smt invar_dim nearest_neighbor sqed_eq_0 sqed_eq_0_rev sqed_ge_0)




text \<open>
  Now generalize the nearest neighbor algorithm to a k nearest neighbor search.  

  Given k-d tree and a point p, which might not be in the tree, find the k closest points ns
  to p by the squared euclidean distance.
\<close>

text\<open>
  The k nearest neighbor algorithm.

  The paper uses a priority queue for the k nearest neighbor candidates.
  I am using a sorted list for simplicity instead.
\<close>

fun k_nearest_neighbors' :: "nat \<Rightarrow> point list \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "k_nearest_neighbors' k ns p (Leaf p') = (
    take k (insort_key (\<lambda>q. sqed q p) p' ns)
  )"
| "k_nearest_neighbors' k ns p (Node a s l r) = (
    if p!a \<le> s then
      let candidates = k_nearest_neighbors' k ns p l in
      if length candidates = k \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        k_nearest_neighbors' k candidates p r
    else
      let candidates = k_nearest_neighbors' k ns p r in
      if length candidates = k \<and> sqed p (last candidates) \<le> sqed' s (p!a) then
        candidates
      else
        k_nearest_neighbors' k candidates p l
  )"




text\<open>Auxiliary lemmas about sorted_wrt for the base cases of the final theorem.\<close>

definition swrtp :: "point \<Rightarrow> point list \<Rightarrow> bool" where
  "swrtp p \<equiv> sorted_wrt (\<lambda>p\<^sub>0 p\<^sub>1. sqed p\<^sub>0 p \<le> sqed p\<^sub>1 p)"

definition insortp :: "point \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> point list" where
  "insortp p \<equiv> insort_key (\<lambda>q. sqed q p)"

declare swrtp_def[simp]
declare insortp_def[simp]

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  have "sorted_wrt f (take n xs @ drop n xs)" 
    using assms by simp
  thus "sorted_wrt f (take n xs)" "sorted_wrt f (drop n xs)"
    using sorted_wrt_append by blast+
qed

lemma sorted_wrt_insort_key:
  "swrtp p ns \<Longrightarrow> swrtp p (insortp p p' ns)"
  apply (induction ns)
  apply (auto)
  by (metis insert_iff le_cases set_insort_key)

lemma sorted_wrt_insort_key_take:
  assumes "swrtp p ns"
  shows "swrtp p (take k (insortp p p' ns))"
proof -
  have "swrtp p (insortp p p' ns)"
    using assms sorted_wrt_insort_key by blast
  thus ?thesis using sorted_wrt_take by auto
qed

lemma
  assumes "swrtp p (xs @ [m] @ ys)"
  shows sorted_wrt_prefix: "\<forall>x \<in> set xs. sqed x p \<le> sqed m p"
  and sorted_wrt_suffix: "\<forall>y \<in> set ys. sqed m p \<le> sqed y p"
  using assms sorted_wrt_append by (simp add: sorted_wrt_append)+

lemma sorted_wrt_last_max:
  assumes "swrtp p ns"
  shows "\<forall>n \<in> set ns. sqed n p \<le> sqed (last ns) p"
proof (cases "ns = []")
  case True
  thus ?thesis by simp
next
  case False
  then obtain ns' m where "ns = ns' @ [m]"
    using rev_exhaust by blast
  hence "swrtp p (ns' @ [m])"
    using assms by blast
  thus ?thesis using sorted_wrt_prefix by (simp add: \<open>ns = ns' @ [m]\<close>)
qed

lemma sorted_wrt_take_elim:
  assumes "swrtp p ns"
  shows "\<forall>n \<in> set ns - set (take k ns). \<forall>n' \<in> set (take k ns). sqed n' p \<le> sqed n p"
proof (cases "k \<ge> length ns")
  case True
  thus ?thesis by simp
next
  case False
  hence "ns = (take k ns) @ [ns!k] @ (drop (k+1) ns)"
    using id_take_nth_drop not_less by auto
  then show ?thesis using assms 
    sorted_wrt_prefix[of p "take k ns" "ns!k" "drop (k+1) ns"]
    sorted_wrt_suffix[of p "take k ns" "ns!k" "drop (k+1) ns"]
    by (smt DiffD1 DiffD2 UnE append_Cons append_Nil set_ConsD set_append)
qed

lemma sorted_wrt_insort_key_take_elim:
  assumes "swrtp p ns"
  shows "\<forall>n \<in> set ns \<union> {p'} - set (take k (insortp p p' ns)). \<forall>n' \<in> set (take k (insortp p p' ns)). sqed n' p \<le> sqed n p"
proof -
  let ?ns' = "insortp p p' ns"
  have "swrtp p ?ns'"
    using assms sorted_wrt_insort_key by blast
  hence "\<forall>n \<in> set ?ns' - set (take k ?ns'). \<forall>n' \<in> set (take k ?ns'). sqed n' p \<le> sqed n p"
    using sorted_wrt_take_elim by blast
  thus ?thesis by (simp add: set_insort_key)
qed

lemma sorted_wrt_take_last_mono:
  assumes "swrtp p ns" "length ns \<ge> k" "k > 0"
  shows "sqed (last (take k ns)) p \<le> sqed (last ns) p"
  using assms
  by (induction ns arbitrary: k) (auto simp add: take_Cons')

lemma sorted_wrt_insort_key_last_eq:
  assumes "swrtp p ns" "insort_key (\<lambda>q. sqed q p) p' ns \<noteq> ns @ [p']"
  shows "last (insortp p p' ns) = last ns"
  using assms
  by (induction ns) (auto)

lemma sorted_wrt_insort_key_take_last_mono:
  assumes "swrtp p ns" "length ns \<ge> k" "k > 0"
  shows "sqed (last (take k (insortp p p' ns))) p \<le> sqed (last ns) p"
proof -
  let ?ns' = "insortp p p' ns"

  show "sqed (last (take k ?ns')) p \<le> sqed (last ns) p"
  proof (cases "?ns' = ns @ [p']")
    case True
    thus ?thesis using assms sorted_wrt_take_last_mono by auto
  next
    case False
    hence EQ: "last ?ns' = last ns"
      using sorted_wrt_insort_key_last_eq assms by simp
    have "sqed (last (take k ?ns')) p \<le> sqed (last ?ns') p"
      using assms sorted_wrt_take_last_mono sorted_wrt_insort_key by simp
    thus ?thesis using EQ by simp
  qed
qed




text\<open>The main lemmas.\<close>

lemma knn_length:
  "length (k_nearest_neighbors' k ns p kdt) = min k (size_kdt kdt + length ns)"
  by (induction kdt arbitrary: ns) (auto simp add: Let_def)

lemma knn_length_gt_0:
  assumes "k > 0"
  shows "length (k_nearest_neighbors' k ns p kdt) > 0"
  using assms
  by (induction kdt arbitrary: ns) (auto simp add: Let_def)

lemma knn_length_gt_eq_k:
  assumes "(set_kdt kdt \<union> set ns) - set (k_nearest_neighbors' k ns p kdt) \<noteq> {}"
  shows "length (k_nearest_neighbors' k ns p kdt) = k"
  using assms knn_length set_insort_key
  apply (induction kdt arbitrary: ns)
  apply (auto simp add: min_def Let_def)
  by fastforce+

lemma knn_sorted:
  assumes "swrtp p ns"
  shows "swrtp p (k_nearest_neighbors' k ns p kdt)"
  using assms sorted_wrt_insort_key_take
  by (induction kdt arbitrary: ns) (auto simp add: Let_def)

lemma knn_set:
  shows "set (k_nearest_neighbors' k ns p kdt) \<subseteq> set_kdt kdt \<union> set ns"
  using set_insort_key in_set_takeD
  apply (induction kdt arbitrary: ns)
  apply (auto simp add: Let_def)
  by fastforce

lemma knn_distinct:
  assumes "invar d kdt" "dim p = d" "distinct ns" "set ns \<inter> set_kdt kdt = {}"
  shows "distinct (k_nearest_neighbors' k ns p kdt)"
  using assms
proof (induction kdt arbitrary: ns)
  case (Leaf p')
  thus ?case by (simp add: distinct_insort)
next
  case (Node a s l r)

  let ?cl = "k_nearest_neighbors' k ns p l"
  let ?cr = "k_nearest_neighbors' k ns p r"

  have "set ns \<inter> set_kdt l = {} \<and> set ns \<inter> set_kdt r = {}"
    using Node.prems(4) by auto
  hence DCLR: "distinct ?cl \<and> distinct ?cr"
    using Node.IH(1,2) Node.prems(1,2,3) invar_l invar_r by blast

  have "set ?cl \<inter> set_kdt r = {} \<and> set ?cr \<inter> set_kdt l = {}"
    using Node.prems(1,4) knn_set invar_distinct by fastforce
  hence "distinct (k_nearest_neighbors' k ?cl p r) \<and> distinct (k_nearest_neighbors' k ?cr p l)"
    using Node.IH(1,2) Node.prems(1,2) DCLR invar_l invar_r by blast

  thus ?case using DCLR by (auto simp add: Let_def)
qed




text\<open>Last auxiliary lemma and the main theorem.\<close>

lemma knn_le_last_ns:
  assumes "invar d kdt" "dim p = d" "swrtp p ns" "length ns \<ge> k" "k > 0"
  shows "sqed (last (k_nearest_neighbors' k ns p kdt)) p \<le> sqed (last ns) p"
  using assms
proof (induction kdt arbitrary: ns)
  case (Leaf p')
  let ?ns' = "take k (insortp p p' ns)"
  have "swrtp p ?ns'"
    using Leaf.prems(3) sorted_wrt_insort_key_take by simp
  hence "\<forall>n \<in> set ?ns'. sqed n p \<le> sqed (last ?ns') p"
    using sorted_wrt_last_max by simp
  hence "\<forall>n \<in> set ?ns'. sqed n p \<le> sqed (last ns) p"
    using Leaf.prems(3,4,5) sorted_wrt_insort_key_take_last_mono by smt
  thus ?case using Leaf.prems(5) by simp
next
  case (Node a s l r)

  let ?cl = "k_nearest_neighbors' k ns p l"
  let ?cr = "k_nearest_neighbors' k ns p r"

  have "length ?cl \<ge> k"
    using knn_length Node.prems(4) by auto
  hence "sqed (last (k_nearest_neighbors' k ?cl p r)) p \<le> sqed (last ?cl) p"
    using knn_sorted Node.IH(2) Node.prems(1,2,3,5) invar_r by blast
  hence IHLR: "sqed (last (k_nearest_neighbors' k ?cl p r)) p \<le> sqed (last ns) p"
    using Node.IH(1) Node.prems invar_l knn_length_gt_0 by smt

  have "length ?cr \<ge> k"
    using knn_length Node.prems(4) by auto
  hence "sqed (last (k_nearest_neighbors' k ?cr p l)) p \<le> sqed (last ?cr) p"
    using knn_sorted Node.IH(1) Node.prems(1,2,3,5) invar_l by blast
  hence IHRL: "sqed (last (k_nearest_neighbors' k ?cr p l)) p \<le> sqed (last ns) p"
    using Node.IH(2) Node.prems invar_r knn_length_gt_0 by smt

  show ?case using Node IHLR IHRL by (auto simp add: Let_def)
qed

theorem knn_sqed:
  assumes "invar d kdt" "dim p = d"
  assumes "swrtp p ns" "set ns \<inter> set_kdt kdt = {}" "distinct ns" "k > 0"
  shows "\<forall>q \<in> set_kdt kdt \<union> set ns - set (k_nearest_neighbors' k ns p kdt). sqed (last (k_nearest_neighbors' k ns p kdt)) p \<le> sqed q p"
  using assms
proof (induction kdt arbitrary: ns)
  case (Leaf p')
  thus ?case using sorted_wrt_insort_key_take_elim by simp
next
  case (Node a s l r)

  let ?cl = "k_nearest_neighbors' k ns p l"
  let ?cr = "k_nearest_neighbors' k ns p r"

  have IHL: "\<forall>q \<in> set_kdt l \<union> set ns - set ?cl. sqed (last ?cl) p \<le> sqed q p"
    using Node.IH(1) Node.prems invar_l invar_set by blast
  have IHR: "\<forall>q \<in> set_kdt r \<union> set ns - set ?cr. sqed (last ?cr) p \<le> sqed q p"
    using Node.IH(2) Node.prems invar_r invar_set by blast

  have SORTED_L: "swrtp p ?cl"
    using knn_sorted Node.prems(3) by blast
  have SORTED_R: "swrtp p ?cr"
    using knn_sorted Node.prems(3) by blast

  have DISTINCT_L: "distinct ?cl"
    using Node.prems(1,2,4,5) knn_distinct invar_set invar_l by blast
  have DISTINCT_R: "distinct ?cr"
    using Node.prems(1,2,4,5) knn_distinct invar_set invar_r by blast

  consider (A) "p!a \<le> s \<and> length ?cl = k \<and> sqed p (last ?cl) \<le> sqed' s (p!a)"
         | (B) "p!a \<le> s \<and> \<not>(length ?cl = k \<and> sqed p (last ?cl) \<le> sqed' s (p!a))"
         | (C) "s < p!a \<and> length ?cr = k \<and> sqed p (last ?cr) \<le> sqed' s (p!a)"
         | (D) "s < p!a \<and> \<not>(length ?cr = k \<and> sqed p (last ?cr) \<le> sqed' s (p!a))"
    by argo
  thus ?case
  proof cases
    case A
    hence "\<forall>q \<in> set_kdt r. sqed (last ?cl) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_r sqed_com by metis
    thus ?thesis using IHL A by auto
  next
    case B

    let ?knn = "k_nearest_neighbors' k ?cl p r"

    have "set ?cl \<subseteq> set_kdt l \<union> set ns \<and> set ns \<inter> set_kdt r = {}"
      using knn_set Node.prems(1,4) by auto
    hence IHLR: "\<forall>q \<in> set_kdt r \<union> set ?cl - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using SORTED_L DISTINCT_L Node.IH(2) Node.prems(1,2,6) invar_r invar_distinct by blast

    have "\<forall>n \<in> set ns - set ?cl. sqed (last ?knn) p \<le> sqed n p"
    proof standard
      fix n
      assume N: "n \<in> set ns - set ?cl"

      hence "length ?cl = k"
        using knn_length_gt_eq_k by blast
      hence LAST: "sqed (last ?knn) p \<le> sqed (last ?cl) p"
        using knn_le_last_ns SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed n p"
        using IHL N by blast
      thus "sqed (last ?knn) p \<le> sqed n p" using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt r \<union> set ns - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using IHLR by auto

    have "\<forall>q \<in> set_kdt l - set ?cl. sqed (last ?knn) p \<le> sqed q p"
    proof standard
      fix q
      assume Q: "q \<in> set_kdt l - set ?cl"

      hence "length ?cl = k"
        using knn_length_gt_eq_k by blast
      hence LAST: "sqed (last ?knn) p \<le> sqed (last ?cl) p"
        using knn_le_last_ns SORTED_L invar_r Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cl) p \<le> sqed q p"
        using IHL Q by blast
      thus "sqed (last ?knn) p \<le> sqed q p" using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt l - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using IHLR by blast

    show ?thesis using B R L by auto
  next
    case C
    hence "\<forall>q \<in> set_kdt l. sqed (last ?cr) p \<le> sqed q p"
      using Node.prems(1,2) cutoff_l sqed_com by smt
    thus ?thesis using IHR C by auto
  next
    case D

    let ?knn = "k_nearest_neighbors' k ?cr p l"

    have "set ?cr \<subseteq> set_kdt r \<union> set ns \<and> set ns \<inter> set_kdt l = {}"
      using knn_set Node.prems(1,4) by auto
    hence IHRL: "\<forall>q \<in> set_kdt l \<union> set ?cr - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using SORTED_R DISTINCT_R Node.IH(1) Node.prems(1,2,6) invar_l invar_distinct by blast

    have "\<forall>n \<in> set ns - set ?cr. sqed (last ?knn) p \<le> sqed n p"
    proof standard
      fix n
      assume N: "n \<in> set ns - set ?cr"

      hence "length ?cr = k"
        using knn_length_gt_eq_k by blast
      hence LAST: "sqed (last ?knn) p \<le> sqed (last ?cr) p"
        using knn_le_last_ns SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed n p"
        using IHR N by blast
      thus "sqed (last ?knn) p \<le> sqed n p" using LAST by argo
    qed
    hence R: "\<forall>q \<in> set_kdt l \<union> set ns - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using IHRL by auto

    have "\<forall>q \<in> set_kdt r - set ?cr. sqed (last ?knn) p \<le> sqed q p"
    proof standard
      fix q
      assume Q: "q \<in> set_kdt r - set ?cr"

      hence "length ?cr = k"
        using knn_length_gt_eq_k by blast
      hence LAST: "sqed (last ?knn) p \<le> sqed (last ?cr) p"
        using knn_le_last_ns SORTED_R invar_l Node.prems(1,2,6) by (metis order_refl)
      have "sqed (last ?cr) p \<le> sqed q p"
        using IHR Q by blast
      thus "sqed (last ?knn) p \<le> sqed q p" using LAST by argo
    qed
    hence L: "\<forall>q \<in> set_kdt r - set ?knn. sqed (last ?knn) p \<le> sqed q p"
      using IHRL by blast

    show ?thesis using D R L by auto
  qed
qed




text\<open>Wrapping up.\<close>

definition k_nearest_neighbors :: "nat \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point list" where
  "k_nearest_neighbors k p kdt = k_nearest_neighbors' k [] p kdt"

theorem k_nearest_neighbors_1:
  assumes "invar d kdt" "dim p = d" "k_nearest_neighbors k p kdt = kns"
  shows "length kns = min k (size_kdt kdt)"
    and "swrtp p kns"
    and "set kns \<subseteq> set_kdt kdt"
    and "distinct kns"
  using assms knn_length knn_sorted knn_set knn_distinct k_nearest_neighbors_def
  apply auto
  by fastforce

theorem k_nearest_neighbors_2:
  assumes "invar d kdt" "dim p = d" "k_nearest_neighbors k p kdt = kns"
  shows "\<forall>q \<in> (set_kdt kdt - set kns). \<forall>n \<in> set kns. sqed n p \<le> sqed q p"
proof -
  have "k > 0 \<longrightarrow> (\<forall>q \<in> set_kdt kdt - set kns. sqed (last kns) p \<le> sqed q p)"
    using assms k_nearest_neighbors_def knn_sqed by auto
  hence "k > 0 \<longrightarrow> (\<forall>q \<in> set_kdt kdt - set kns. \<forall>n \<in> set kns. sqed n p \<le> sqed q p)"
    by (smt assms k_nearest_neighbors_1(2) sorted_wrt_last_max)
  thus "\<forall>q \<in> (set_kdt kdt - set kns). \<forall>n \<in> set kns. sqed n p \<le> sqed q p"
    using assms k_nearest_neighbors_def k_nearest_neighbors_1(1) by (metis length_pos_if_in_set min_less_iff_conj)
qed




(* FROM HERE ON ONLY ADOPTED PROOFS FROM LAST SEMESTER *)

text \<open>
  Verifying d-dimensional queries on the k-d tree.

  Given two d-dimensional points p0 and p1 which bound the search space, the query should return
  only the points which satisfy the following criteria:

  For every point p in the resulting set:
    For every axis a \<in> [0, d-1]:
      min (p0!a) (p1!a) <= p!a and p!a <= max (p0!a) (p1!a)

  For example: In a 2-d tree a query corresponds to selecting all the points in
  the rectangle which has p0 and p1 as its defining edges.
\<close>

text \<open>
  Simplifying the problem:

  Assume that the two given points p0 and p1 which define the bounding box are the left lower
  and the right upper point.

  For every point p in the resulting set:
    For every axis a \<in> [0, d-1]:
      p0!a <= p1!a
\<close>

text\<open>The query function and auxiliary definitions:\<close>

definition is_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "is_bounding_box d p\<^sub>0 p\<^sub>1 \<longleftrightarrow> dim p\<^sub>0 = d \<and> dim p\<^sub>1 = d \<and> (\<forall>i < d. p\<^sub>0!i \<le> p\<^sub>1!i)"

definition point_in_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "point_in_bounding_box d p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < d. p\<^sub>0!i \<le> p!i \<and> p!i \<le> p\<^sub>1!i)"

fun query_area' :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area' d p\<^sub>0 p\<^sub>1 (Leaf p) = (
    if point_in_bounding_box d p p\<^sub>0 p\<^sub>1 then {p} else {}
  )"
| "query_area' d p\<^sub>0 p\<^sub>1 (Node a s l r) = (
    if s < p\<^sub>0!a then
      query_area' d p\<^sub>0 p\<^sub>1 r
    else if p\<^sub>1!a \<le> s then
      query_area' d p\<^sub>0 p\<^sub>1 l
    else
      query_area' d p\<^sub>0 p\<^sub>1 l \<union> query_area' d p\<^sub>0 p\<^sub>1 r
  )"




text \<open>Auxiliary lemmas:\<close>

lemma l_pibb_empty:
  assumes "invar d (Node a s l r)" "s < p\<^sub>0!a"
  shows "{ p \<in> set_kdt l. point_in_bounding_box d p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt l. p!a < p\<^sub>0!a"
    using invar_l_le_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt l. (\<exists>i < d. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_d by blast
  hence "\<forall>p \<in> set_kdt l. \<not>point_in_bounding_box d p p\<^sub>0 p\<^sub>1"
    using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

lemma r_pibb_empty:
  assumes "invar d (Node a s l r)" "p\<^sub>1!a \<le> s"
  shows "{ p \<in> set_kdt r. point_in_bounding_box d p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>p \<in> set_kdt r. p\<^sub>1!a < p!a"
    using invar_r_gt_a assms(1,2) by auto
  hence "\<forall>p \<in> set_kdt r. (\<exists>i < d. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(1) invar_axis_lt_d by blast
  hence "\<forall>p \<in> set_kdt r. \<not>point_in_bounding_box d p p\<^sub>0 p\<^sub>1"
   using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed




text \<open>The simplified main theorem:\<close>

theorem query_area':
  assumes "invar d kdt"
  shows "query_area' d p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box d p p\<^sub>0 p\<^sub>1 }"
  using assms l_pibb_empty r_pibb_empty
  by (induction kdt) auto




text \<open>
  Un-simplifying the problem:

  Given two arbitrary points p0 and p1 which only satisfy the dimensionality property,
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
  assumes "dim q\<^sub>0 = d" "dim q\<^sub>1 = d" "(p\<^sub>0 ,p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "is_bounding_box d p\<^sub>0 p\<^sub>1"
  using assms by (auto simp add: to_bounding_box_def is_bounding_box_def)

lemma pibb:
  assumes "dim q\<^sub>0 = d" "dim q\<^sub>1 = d" "(p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "point_in_bounding_box d p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < d. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i))"
  using assms by (auto simp add: min_def max_def to_bounding_box_def point_in_bounding_box_def)

theorem query_area:
  assumes "invar d kdt" "dim q\<^sub>0 = d" "dim q\<^sub>1 = d"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < d. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> x!i \<and> x!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i) }"
  using assms pibb tbbibb query_area' by (auto simp add: query_area_def)

corollary
  assumes "invar d kdt" "dim q\<^sub>0 = d" "dim q\<^sub>1 = d"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = query_area q\<^sub>1 q\<^sub>0 kdt"
  using assms query_area by auto

corollary
  assumes "invar d kdt" "dim q\<^sub>0 = d" "dim q\<^sub>1 = d" 
  assumes "p \<in> set_kdt kdt" "\<forall>i < d. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i)"
  shows "p \<in> query_area q\<^sub>0 q\<^sub>1 kdt"
  using assms query_area by blast

corollary
  assumes "invar d kdt" "dim q\<^sub>0 = d" "q\<^sub>0 = q\<^sub>1" "q\<^sub>0 \<in> set_kdt kdt"
  shows "query_area q\<^sub>0 q\<^sub>1 kdt = { q\<^sub>0 }"
proof -
  have QA: "query_area q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < d. q\<^sub>0!i = x!i }"
    using query_area assms(1,2,3) by auto

  have A: "\<forall>p \<in> query_area q\<^sub>0 q\<^sub>1 kdt. dim p = d"
    using assms(1) QA invar_dim by blast
  have B: "q\<^sub>0 \<in> query_area q\<^sub>0 q\<^sub>1 kdt"
    using assms(4) QA by blast
  have C: "\<forall>p \<noteq> q\<^sub>0. dim p = d \<longrightarrow> (\<exists>i < d. q\<^sub>0!i \<noteq> p!i)"
    using assms(2) nth_equalityI by fastforce

  show ?thesis using QA A B C by blast
qed

end