theory homework_10
imports
  Complex_Main
begin

text \<open>
  I did take "Functional Data Structures" last semester and verified the range query algorithm
  as final project. Those sections are marked (LINE 130-286) and should not be graded but 
  are here for completeness only.

  The construction of balanced k-d trees and the nearest neighbor algorithm are new.
  There is of course some overlap in the initial definitions but I had to change the tree
  by moving the data form the nodes to the leafs to make the nearest neighbor algorithm work and
  adjust the work from last semester accordingly.
\<close>

text \<open>
  A k-d tree is a space-partitioning data structure for organizing points in a k-dimensional space.
  In principle the k-d tree is a binary tree. The leafs hold the k-dimensional points and the nodes
  contain left and right subtrees as well as a splitting value at a particular axis.
  The tree could also be build with the nodes holding the points and the leafs being empty, but this
  complicates the code and the proofs.
  Every node divides the space into two parts by splitting along a hyperplane.
  Consider a node n with associated split s in depth d, counting the number of edges from the root.
  The splitting hyperplane of this point will be the (d mod k) axis with value s.
  Subsequently all points in the left subtree must have a value at axis (d mod k) that is less or
  equal than s and all points in the right subtree must have a value at axis (d mod k) that is
  greater that v.

  e.g.: Consider a 2-d tree.

   0/x-axis:                          N 7

   1/y-axis:                N 3                 N 6

   0/x-axis:         N 2          N 4      (9,6)     N 8

                 (2,3) (7, 2)  (4,7) (5,4)       (8,7) (9,9)

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
| Node kdt split kdt

definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

definition incr :: "axis \<Rightarrow> dimension \<Rightarrow> axis" where
  "incr a d = (a + 1) mod d"

declare dim_def[simp]
declare incr_def[simp]




text \<open> 
  Abstraction function and invariant.
  Some lemmas for conveniently working with the invariant.
\<close>

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt (Leaf p) = {p}"
| "set_kdt (Node l _ r) = set_kdt l \<union> set_kdt r"

fun invar' :: "axis \<Rightarrow> dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar' _ k (Leaf p) \<longleftrightarrow> k > 0 \<and> dim p = k"
| "invar' a k (Node l s r) \<longleftrightarrow> (\<forall>p \<in> set_kdt l. p!a \<le> s) \<and> (\<forall>p \<in> set_kdt r. p!a > s) \<and>
    invar' (incr a k) k l \<and> invar' (incr a k) k r"

abbreviation invar where
  "invar \<equiv> invar' 0"

lemma invar'_l:
  assumes "invar' a k (Node l s r)"
  shows "invar' (incr a k) k l"
  using assms by simp

lemma invar'_r:
  assumes "invar' a k (Node l s r)"
  shows "invar' (incr a k) k r"
  using assms by simp

lemma invar'_dim_gt_0:
  assumes "invar' a k kdt"
  shows "k > 0"
  using assms by (induction kdt arbitrary: a) auto
  
lemma invar'_dim:
  assumes "invar' a k kdt"
  shows "\<forall>p \<in> set_kdt kdt. dim p = k"
  using assms by (induction kdt arbitrary: a) auto

lemma invar'_l_le_a: 
  assumes "invar' a k kdt" "kdt = Node l s r"
  shows "\<forall>p \<in> set_kdt l. p!a \<le> s"
  using assms invar'.simps(2) by blast

lemma invar'_r_gt_a: 
  assumes "invar' a k kdt" "kdt = Node l s r"
  shows "\<forall>p \<in> set_kdt r. s < p!a"
  using assms invar'.simps(2) by blast




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

fun query_area' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area' _ k p\<^sub>0 p\<^sub>1 (Leaf p) = (
    if point_in_bounding_box k p p\<^sub>0 p\<^sub>1 then {p} else {}
  )"
| "query_area' a k p\<^sub>0 p\<^sub>1 (Node l s r) = (
    let a' = incr a k in
    if s < p\<^sub>0!a then
      query_area' a' k p\<^sub>0 p\<^sub>1 r
    else if s > p\<^sub>1!a then
      query_area' a' k p\<^sub>0 p\<^sub>1 l
    else
      query_area' a' k p\<^sub>0 p\<^sub>1 l \<union> query_area' a' k p\<^sub>0 p\<^sub>1 r
  )"




text \<open>Auxiliary lemmas:\<close>

lemma l_pibb_empty:
  assumes "invar' a k kdt" "kdt = Node l s r" "is_bounding_box k p\<^sub>0 p\<^sub>1" "s < p\<^sub>0!a" "a < k"
  shows "{ p \<in> set_kdt l. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>q \<in> set_kdt l. q!a \<le> s"
    using assms(1,2) invar'_l_le_a by blast
  hence "\<forall>p \<in> set_kdt l. p!a < p\<^sub>0!a"
    using assms(4) by auto
  hence "\<forall>p \<in> set_kdt l. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(5) by blast
  hence "\<forall>p \<in> set_kdt l. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
    using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

lemma r_pibb_empty:
  assumes "invar' a k kdt" "kdt = Node l s r" "is_bounding_box k p\<^sub>0 p\<^sub>1" "s > p\<^sub>1!a " "a < k"
  shows "{ p \<in> set_kdt r. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>q \<in> set_kdt r. s < q!a"
    using assms(1,2) invar'_r_gt_a by blast
  hence "\<forall>p \<in> set_kdt r. p\<^sub>1!a < p!a"
    using assms(4) by auto
  hence "\<forall>p \<in> set_kdt r. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(5) by blast
  hence "\<forall>p \<in> set_kdt r. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
   using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed




text \<open>The simplified main theorem:\<close>

theorem query_area':
  assumes "invar' a k kdt" "is_bounding_box k p\<^sub>0 p\<^sub>1" "a < k"
  shows "query_area' a k p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms l_pibb_empty r_pibb_empty
  by (induction kdt arbitrary: a) (auto simp add: Let_def)




text \<open>
  I would like to drop explicitly passing the splitting axis into every function.
  The corresponding query function and lemmas in shorter form:
\<close>

definition query_area :: "point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area p\<^sub>0 p\<^sub>1 kdt = query_area' 0 (dim p\<^sub>0) p\<^sub>0 p\<^sub>1 kdt"

theorem query_area:
  assumes "invar k kdt" "is_bounding_box k p\<^sub>0 p\<^sub>1"
  shows "query_area p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms invar'_dim_gt_0 is_bounding_box_def query_area' query_area_def by auto




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

definition query :: "point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query q\<^sub>0 q\<^sub>1 kdt = (let (p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1 in query_area p\<^sub>0 p\<^sub>1 kdt)"




text \<open>Auxiliary lemmas and the final theorem:\<close>

lemma tbbibb:
  assumes "k = dim q\<^sub>0" "k = dim q\<^sub>1" "(p\<^sub>0 ,p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "is_bounding_box k p\<^sub>0 p\<^sub>1"
  using assms by (auto simp add: to_bounding_box_def is_bounding_box_def)

lemma pibb:
  assumes "k = dim q\<^sub>0" "k = dim q\<^sub>1" "(p\<^sub>0, p\<^sub>1) = to_bounding_box q\<^sub>0 q\<^sub>1"
  shows "point_in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> p!i \<and> p!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i))"
  using assms by (auto simp add: min_def max_def to_bounding_box_def point_in_bounding_box_def)

theorem query:
  assumes "invar k kdt" "k = dim q\<^sub>0" "k = dim q\<^sub>1"
  shows "query q\<^sub>0 q\<^sub>1 kdt = { x \<in> set_kdt kdt. \<forall>i < k. min (q\<^sub>0!i) (q\<^sub>1!i) \<le> x!i \<and> x!i \<le> max (q\<^sub>0!i) (q\<^sub>1!i) }"
  using assms pibb tbbibb query_area by (auto simp add: query_def)

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




text\<open>
  The nearest neighbor algorithm.
\<close>

fun nearest_neighbor' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor' _ _ _ (Leaf p) = p"
| "nearest_neighbor' a k p (Node l s r) = (
    if p!a \<le> s then
      let candidate = nearest_neighbor' (incr a k) k p l in
      if sqed p candidate \<le> sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor' (incr a k) k p r in
        min_by_sqed candidate candidate' p
    else
      let candidate = nearest_neighbor' (incr a k) k p r in
      if sqed p candidate < sqed' s (p!a) then
        candidate
      else
        let candidate' = nearest_neighbor' (incr a k) k p l in
        min_by_sqed candidate candidate' p
  )"




text \<open>First part of main theorem as warm up.\<close>

lemma nearest_neighbor'_in_kdt:
  assumes "invar' a k kdt" "dim p = k"
  shows "nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms by (induction kdt arbitrary: a) (auto simp add: Let_def min_by_sqed_def)



text \<open>Second part of main theorem.\<close>

text \<open>Auxiliary lemmas.\<close>

text \<open>
  Some intuition about this step:

  Scenario A:
  We are searching for the nearest neighbor of point p and have found candidate c.
  Since sqed c p <= sqed' s (p!a) we do not need to check the right side.

                                s
          c                     |
                                |
               p                |     
                                |   
                                |  q
                                |


  Scenario B:
  We are searching for the nearest neighbor of point p and have found candidate c.
  Since sqed c p > sqed' s (p!a) we do need to check the right side.

                                s
          c                     |
                                |
                          p     |  q'   
                                |   
                                |  q
                                |

  The minimize_sqed lemma moves q to q' by setting all coordinates of q' (except the current axis)
  to the coordinates of p and so minimizes the distance between p and q'.

  On the symmetric case the inequality is strict since the left subtree contains points <= s and the
  right subtree contains points > s.
\<close>

lemma minimize_sqed:
  assumes "dim p\<^sub>0 = k" "dim p\<^sub>1 = k" "a < k"
  shows "sqed p\<^sub>0 p\<^sub>1 \<ge> sqed' (p\<^sub>0!a) (p\<^sub>0[a := (p\<^sub>1!a)]!a)"
  using assms
  apply (induction p\<^sub>0 p\<^sub>1 arbitrary: a k rule: sqed.induct)
  apply (auto simp add: sqed_ge_0 split: nat.splits)
  by (smt sqed'_ge_0)

lemma cutoff_r:
  assumes "invar' a k (Node l s r)" "p!a \<le> s" "c \<in> set_kdt l" "dim p = k" "a < k" "sqed p c \<le> sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt r. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt r"

  let ?q' = "p[a := (q!a)]"

  (* The distance between p and q is greater or equal the minimized distance between p and q' *)
  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,4,5) invar'_dim invar'_r by blast
  (* Hence it is greater or equal to the distance from p to s + the distance from s to q' *)
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,4,5) dim_def nth_list_update_eq invar'_r_gt_a sqed'_split)
  (* Hence it is greater or equal to the distance from p to c since sqed' s (q!a) \<ge> 0 *)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(6) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed

lemma cutoff_l:
  assumes "invar' a k (Node l s r)" "p!a > s" "c \<in> set_kdt r" "dim p = k" "a < k" "sqed p c < sqed' s (p!a)"
  shows "\<forall>q \<in> set_kdt l. sqed p c \<le> sqed p q"
proof standard
  fix q
  assume A: "q \<in> set_kdt l"

  let ?q' = "p[a := (q!a)]"

  have "sqed p q \<ge> sqed' (p!a) (?q'!a)"
    using A minimize_sqed assms(1,4,5) invar'_dim invar'_l by blast
  hence "sqed p q \<ge> sqed' (p!a) s + sqed' s (q!a)"
    by (smt A assms(1,2,4,5) dim_def invar'_l_le_a nth_list_update_eq sqed'_com sqed'_split)
  hence "sqed p q \<ge> sqed p c"
    by (smt assms(6) sqed'_com sqed'_ge_0)

  thus "sqed p c \<le> sqed p q" by blast
qed




text \<open>The main proof and the final theorem.\<close>

lemma nearest_neighbor'_minimal:
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor' a k p kdt) p \<le> sqed q p"
  using assms
proof (induction kdt arbitrary: a)
  case (Leaf p)
  thus ?case by simp                                      
next
  case (Node l s r)
  let ?candidate_l = "nearest_neighbor' (incr a k) k p l"
  let ?candidate_r = "nearest_neighbor' (incr a k) k p r"

  have IHL: "\<forall>q \<in> set_kdt l. sqed ?candidate_l p \<le> sqed q p"
    using Node.IH(1) Node.prems(1,3) assms(2) by auto
  have IHR: "\<forall>q \<in> set_kdt r. sqed ?candidate_r p \<le> sqed q p"
    using Node.IH(2) Node.prems(1,3) assms(2) by auto
 
  have CUTOFF_L: "s < p!a \<longrightarrow> sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> (\<forall>q \<in> set_kdt l. sqed p ?candidate_r \<le> sqed p q)"
    using Node.prems(1,3) assms(2) cutoff_l invar'_r nearest_neighbor'_in_kdt by blast
  have CUTOFF_R: "p!a \<le> s \<longrightarrow> sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> (\<forall>q \<in> set_kdt r. sqed p ?candidate_l \<le> sqed p q)"
    using Node.prems(1,3) assms(2) cutoff_r invar'_l nearest_neighbor'_in_kdt by blast

  have LY: "p!a \<le> s \<longrightarrow> sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL CUTOFF_R apply (auto) by (metis assms(2) invar'_dim nearest_neighbor'_in_kdt sqed_com)
  have LN: "p!a \<le> s \<longrightarrow> \<not>sqed p ?candidate_l \<le> sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)

  have RY: "s < p!a \<longrightarrow> sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHR CUTOFF_L apply (auto) by (metis (mono_tags, lifting) assms(2) invar'_dim nearest_neighbor'_in_kdt sqed_com)
  have RN: "s < p!a \<longrightarrow> \<not>sqed p ?candidate_r < sqed' s (p!a) \<longrightarrow> ?case"
    using Node.prems IHL IHR by (auto simp add: min_by_sqed_def Let_def)

  show ?case using LY LN RY RN by argo
qed

theorem nearest_neighbor':
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor' a k p kdt) p \<le> sqed q p) \<and> nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor'_in_kdt nearest_neighbor'_minimal by simp




text \<open>
  I would like to drop explicitly passing the splitting axis into every function.
  Define abbreviations and start splitting at 0th axis.
\<close>

definition nearest_neighbor :: "point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor p = nearest_neighbor' 0 (dim p) p"

lemma nearest_neighbor_in_kdt:
  assumes "invar k kdt" "dim p = k"
  shows "nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms by (simp add: nearest_neighbor'_in_kdt nearest_neighbor_def)

lemma nearest_neighbor_minimal:
  assumes "invar k kdt" "dim p = k"
  shows "\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p"
  using assms by (simp add: invar'_dim_gt_0 nearest_neighbor'_minimal nearest_neighbor_def)

theorem nearest_neighbor:
  assumes "invar k kdt" "dim p = k"
  shows "(\<forall>q \<in> set_kdt kdt. sqed (nearest_neighbor p kdt) p \<le> sqed q p) \<and> nearest_neighbor p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor_in_kdt nearest_neighbor_minimal by simp




(* *** *)
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
      select a hps (k - length ps)
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

end