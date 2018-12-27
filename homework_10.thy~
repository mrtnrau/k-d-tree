theory homework_10
imports
  Complex_Main
begin

text \<open>
  I did take "Functional Data Structures" last semester and verified the range query algorithm
  as final project. Those sections are marked (LINE 125-260) and have already been graded but
  are here for completeness only.

  The construction of balanced k-d trees and the nearest neighbor algorithm are new.
  There is of course some overlap in the initial definitions but I had to change the tree
  by moving the data form the nodes to the leafs and storing the axis in the node to make the
  nearest neighbor algorithm work and adjust the work from last semester accordingly.
\<close>

text \<open>
  A k-d tree is a space-partitioning data structure for organizing points in a k-dimensional space.
  In principle the k-d tree is a binary tree. The leafs hold the k-dimensional points and the nodes
  contain left and right subtrees as well as a splitting value at a particular axis.
  The tree could also be build with the nodes holding the points and the leafs being empty, but this
  complicates the code and the proofs.
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

  Friedman, J. (1976). "An Algroithm for Finding Best Matches in Logarithmic Expected Time".
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

fun invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar k (Leaf p) \<longleftrightarrow> dim p = k"
| "invar k (Node a s l r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> s) \<and> (\<forall>p \<in> set_kdt r. p!a \<ge> s) \<and>
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
  shows "\<forall>p \<in> set_kdt r. s \<le> p!a"
  using assms by simp




(* THIS IS FROM LAST SEMESTER START *)

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
    else if p\<^sub>1!a < s then
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
  assumes "invar k (Node a s l r)" "p\<^sub>1!a < s"
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

(* THIS IS FROM LAST SEMESTER END *)




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
  using sqed'_def by simp

lemma sqed'_eq_0[simp]:
  "sqed' x y = 0 \<longleftrightarrow> x = y"
  using sqed'_def by simp

lemma sqed'_com:
  "sqed' x y = sqed' y x"
  using sqed'_def by (simp add: power2_commute)

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
  using assms by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_ge_0)

lemma sqed_eq_0[simp]:
  assumes "p\<^sub>0 = p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = 0"
  using assms by(induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) auto

lemma sqed_com:
  assumes "dim p\<^sub>0 = dim p\<^sub>1"
  shows "sqed p\<^sub>0 p\<^sub>1 = sqed p\<^sub>1 p\<^sub>0"
  using assms by (induction p\<^sub>0 p\<^sub>1 rule: sqed.induct) (auto simp add: sqed'_com)




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
  assumes "invar k kdt" "dim p = k"
  shows "nearest_neighbor k p kdt \<in> set_kdt kdt"
  using assms by (induction kdt) (auto simp add: Let_def min_by_sqed_def)



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




(* *** *)

fun partition :: "nat \<Rightarrow> nat list \<Rightarrow> (nat list * nat list)" where
  "partition _ [] = ([], [])"
| "partition p (x # xs) = (
    let (ls, hs) = partition p xs in
    if x \<le> p then
      (x # ls, hs)
    else
      (ls, x # hs)
  )"

fun select :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "select [] _ = undefined"
| "select [x] _ = x"
| "select (x # xs) k = (
    let (ls, hs) = partition x xs in
    if k = length xs then
      x
    else if k < length xs then
      select ls k
    else
      select hs (k - length ls - 1)
  )"
termination
  apply size_change
  done

(*
fun partition :: "axis \<Rightarrow> point \<Rightarrow> point list \<Rightarrow> (point list * point list)" where
  "partition _ _ [] = ([], [])"
| "partition a p (x # xs) = (
    let (as, bs) = partition a p xs in
    if x!a \<le> p!a then
      (x # as, bs)
    else
      (as, x # bs)
  )"

fun select :: "axis \<Rightarrow> point list \<Rightarrow> nat \<Rightarrow> point" where
  "select _ [] _ = undefined"
| "select _ [p] _ = p"
| "select a (p # ps) k = (
    let (lps, hps) = partition a p ps in
    if k = length ps then
      p
    else if k < length ps then
      select a lps k
    else
      select a hps (k - length lps - 1)
  )"
termination
  apply size_change
  done

lemma partition_left_lt_or_eq:
  "\<forall>p' \<in> set (fst (partition a p ps)). p'!a \<le> p!a"
  by (induction ps) (auto split: prod.splits)

lemma partition_right_gt:
  "\<forall>p' \<in> set (snd (partition a p ps)). p'!a > p!a"
  by (induction ps) (auto split: prod.splits)

lemma partition_length:
  "length ps = length (fst (partition a p ps)) + length (snd (partition a p ps))"
  by (induction ps) (auto split: prod.splits)

lemma partition:
  "set ps = set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
proof standard
  show "set ps \<subseteq> set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
    by (induction ps) (auto split: prod.splits)
next
  show "set ps \<supseteq> set (fst (partition a p ps)) \<union> set (snd (partition a p ps))"
  by (induction ps) (auto split: prod.splits)
qed
*)

end
