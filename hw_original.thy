theory hw_original
imports
  Complex_Main
  "~~/src/HOL/Library/Tree"
begin

text \<open>
  A k-d tree is a space-partitioning data structure for organizing points in a k-dimensional space.
  In principle the k-d tree is a binary tree in which every node is a k-dimensional point.
  Every node divides the space into two parts by splitting along a hyperplane.
  Consider a node n with associated point p in depth d, counting the number of edges from the root.
  The splitting hyperplane of this point will be the (d mod k) axis of the associated point p.
  Let v be the value of p at axis (d mod k). Subsequently all points in the left subtree must have
  a value at axis (d mod k) that is less or equal than v and all points in the right subtree must
  have a value at axis (d mod k) that is greater than v.

  e.g.: Consider a 2-d tree.

   0/x-axis:                      (7, 2)

   1/y-axis:           (5,4)               (9,6)

   0/x-axis:    (2,3)        (4,7)                (8,7)
\<close>

text \<open>Synonyms for point, axis, dimension and k-d tree.\<close>

type_synonym point = "real list"
type_synonym axis = nat
type_synonym dimension = nat
type_synonym kdt = "point tree"

definition dim :: "point \<Rightarrow> nat"  where
  "dim p = length p"

definition incr :: "axis \<Rightarrow> dimension \<Rightarrow> axis" where
  "incr a d = (a + 1) mod d"

declare dim_def[simp]
declare incr_def[simp]

text \<open>
  First Part:

  Defining the invariant, abstraction and defining insertion into a k-d tree and membership of
  a k-d tree.
\<close>

text \<open>Abstraction function relating k-d tree to set:\<close>

fun set_kdt :: "kdt \<Rightarrow> point set" where
  "set_kdt Leaf         = {}"
| "set_kdt (Node l p r) = {p} \<union> set_kdt l \<union> set_kdt r"

text \<open>The k-d tree invariant:\<close>

fun invar' :: "axis \<Rightarrow> dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "invar' _ k Leaf \<longleftrightarrow> k > 0"
| "invar' a k (Node l p r) \<longleftrightarrow> dim p = k \<and> (\<forall>q \<in> set_kdt l. \<exists>i < k. q!i \<noteq> p!i) \<and>
    (\<forall>q \<in> set_kdt l. q!a \<le> p!a) \<and> (\<forall>q \<in> set_kdt r. q!a > p!a) \<and>
    invar' (incr a k) k l \<and> invar' (incr a k) k r"

text \<open>Insertion:\<close>

fun ins_kdt' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> kdt" where
  "ins_kdt' _ _ p Leaf = Node Leaf p Leaf"
| "ins_kdt' a k p (Node l p' r) = (
    if p = p' then Node l p' r
    else
      let a' = incr a k in
      if p!a \<le> p'!a then
        Node (ins_kdt' a' k p l) p' r
      else
        Node l p' (ins_kdt' a' k p r)
  )"

text \<open>Membership:\<close>

fun isin_kdt' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> bool" where
  "isin_kdt' _ _ _ Leaf = False"
| "isin_kdt' a k p (Node l p' r) = (
    if p = p' then True
    else
      let a' = incr a k in
      if p!a \<le> p'!a then
        isin_kdt' a' k p l
      else
        isin_kdt' a' k p r
  )"

text \<open>Lemmas about Insertion and Membership:\<close>

lemma set_ins_kdt':
  "set_kdt (ins_kdt' a k p kdt) = set_kdt kdt \<union> {p}"
  by (induction kdt arbitrary: a) (auto simp add: Let_def)

lemma invar_ins_kdt': 
  assumes "invar' a k kdt" "dim p = k" 
  shows "invar' a k (ins_kdt' a k p kdt)"
  using assms 
  apply (induction kdt arbitrary: a) 
  apply (auto simp add: set_ins_kdt' Let_def)
  using nth_equalityI by fastforce

lemma isin_kdt':
  assumes "invar' a k kdt"
  shows "isin_kdt' a k p kdt \<longleftrightarrow> p \<in> set_kdt kdt"
  using assms(1) by (induction kdt arbitrary: a) auto

text \<open>
  I would like to drop explicitly passing the splitting axis into every function.
  Define abbreviations and start splitting at 0th axis.
  The corresponding Insertion and Membership functions and lemmas in shorter form:
\<close>

abbreviation invar where
  "invar \<equiv> invar' 0"

definition ins_kdt :: "point \<Rightarrow> kdt \<Rightarrow> kdt" where
  "ins_kdt p = ins_kdt' 0 (dim p) p"

definition isin_kdt :: "point \<Rightarrow> kdt \<Rightarrow> bool" where
  "isin_kdt p = isin_kdt' 0 (dim p) p"

lemma set_ins_kdt: 
  "set_kdt (ins_kdt p kdt) = set_kdt kdt \<union> {p}"
  by (simp add: set_ins_kdt' ins_kdt_def)

lemma invar_ins_kdt: 
  assumes "invar k kdt" "dim p = k" 
  shows "invar k (ins_kdt p kdt)"
  using assms by (simp add: invar_ins_kdt' ins_kdt_def)

lemma isin_kdt: 
  assumes "invar k kdt" "dim p = k" 
  shows "isin_kdt p kdt \<longleftrightarrow> p \<in> set_kdt kdt"
  using assms by (simp add: isin_kdt' isin_kdt_def)

text \<open>
  Second Part:

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

  Assume that the two given points p\<^sub>0 and p\<^sub>1  which define the bounding box are the left lower
  and the right upper point.

  For every axis a \<in> [0, k-1]:
    p\<^sub>0!a <= p\<^sub>1!a
\<close>

text\<open>The query function and auxiliary definitions:\<close>

definition is_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "is_bounding_box k p\<^sub>0 p\<^sub>1 \<longleftrightarrow> dim p\<^sub>0 = k \<and> dim p\<^sub>1 = k \<and> (\<forall>i < k. p\<^sub>0!i \<le> p\<^sub>1!i)"

definition point_in_bounding_box :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool" where
  "point_in_bounding_box k p p\<^sub>0 p\<^sub>1 \<longleftrightarrow> (\<forall>i < k. p\<^sub>0!i \<le> p!i \<and> p!i \<le> p\<^sub>1!i)"

fun query_area' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area' _ _ _ _ Leaf = {}"
| "query_area' a k p\<^sub>0 p\<^sub>1 (Node l p r) = (
    let a' = incr a k in
    if point_in_bounding_box k p p\<^sub>0 p\<^sub>1 then
      {p} \<union> query_area' a' k p\<^sub>0 p\<^sub>1 l \<union> query_area' a' k p\<^sub>0 p\<^sub>1 r
    else
      if p!a < p\<^sub>0!a then
        query_area' a' k p\<^sub>0 p\<^sub>1 r
      else if p!a > p\<^sub>1!a then
        query_area' a' k p\<^sub>0 p\<^sub>1 l
      else
        query_area' a' k p\<^sub>0 p\<^sub>1 l \<union> query_area' a' k p\<^sub>0 p\<^sub>1 r
  )"

text \<open>Auxiliary lemmas:\<close>

lemma set_kdt_l_lq_a: 
  assumes "invar' a k kdt" "kdt = Node l p r"
  shows "\<forall>q \<in> set_kdt l. q!a \<le> p!a"
  using assms by (induction kdt arbitrary: a) auto

lemma set_kdt_r_gt_a: 
  assumes "invar' a k kdt" "kdt = Node l p r"
  shows "\<forall>q \<in> set_kdt r. p!a < q!a"
  using assms by (induction kdt arbitrary: a) auto

lemma invar'_dim_gt_0: "invar' a k kdt \<Longrightarrow> k > 0"
  by (induction kdt arbitrary: a) auto

lemma l_pibb_empty:
  assumes "invar' a k kdt" "kdt = Node l p r" "is_bounding_box k p\<^sub>0 p\<^sub>1" "p!a < p\<^sub>0!a" "a < k"
  shows "{ p \<in> set_kdt l. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>q \<in> set_kdt l. q!a \<le> p!a"
    using set_kdt_l_lq_a assms(1) assms(2) by blast
  hence "\<forall>p \<in> set_kdt l. p!a < p\<^sub>0!a"
    using assms(4) by auto
  hence "\<forall>p \<in> set_kdt l. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(5) by blast
  hence "\<forall>p \<in> set_kdt l. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
    using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

lemma r_pibb_empty:
  assumes "invar' a k kdt" "kdt = Node l p r" "is_bounding_box k p\<^sub>0 p\<^sub>1" "p!a > p\<^sub>1!a" "a < k"
  shows "{ p \<in> set_kdt r. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 } = {}"
  using assms
proof -
  have "\<forall>q \<in> set_kdt r. p!a < q!a"
    using set_kdt_r_gt_a assms(1) assms(2) by blast
  hence "\<forall>p \<in> set_kdt r. p\<^sub>1!a < p!a"
    using assms(4) by auto
  hence "\<forall>p \<in> set_kdt r. (\<exists>i < k. p!i < p\<^sub>0!i \<or> p\<^sub>1!i < p!i)"
    using assms(5) by blast
  hence "\<forall>p \<in> set_kdt r. \<not>point_in_bounding_box k p p\<^sub>0 p\<^sub>1"
   using point_in_bounding_box_def by fastforce
  thus ?thesis by blast
qed

text \<open>The main theorem:\<close>

theorem query_area':
  assumes "invar' a k kdt" "is_bounding_box k p\<^sub>0 p\<^sub>1" "a < k"
  shows "query_area' a k p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms l_pibb_empty r_pibb_empty
  by (induction kdt arbitrary: a) (auto simp add: Let_def)

text \<open>
  Again I would like to drop explicitly passing the splitting axis into every function.
  The corresponding query function and lemmas in shorter form:
\<close>

definition query_area :: "point \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point set" where
  "query_area p\<^sub>0 p\<^sub>1 kdt = query_area' 0 (dim p\<^sub>0) p\<^sub>0 p\<^sub>1 kdt"

theorem query_area:
  assumes "invar k kdt" "is_bounding_box k p\<^sub>0 p\<^sub>1"
  shows "query_area p\<^sub>0 p\<^sub>1 kdt = { p \<in> set_kdt kdt. point_in_bounding_box k p p\<^sub>0 p\<^sub>1 }"
  using assms invar'_dim_gt_0 is_bounding_box_def query_area' query_area_def by auto

text \<open>
  Finally un-simplifying the problem:

  Given two arbitrary points p\<^sub>0 and p\<^sub>1 which only satisfy the dimensionality property,
  does the query function work?

  Hide the is_bounding_box abstraction:
\<close>

text \<open>Auxiliary functions and the final query function:\<close>

fun min_max :: "real * real \<Rightarrow> real * real" where
  "min_max (a, b) = (min a b, max a b)"

definition to_bounding_box :: "point \<Rightarrow> point \<Rightarrow> point * point" where
  "to_bounding_box q\<^sub>0 q\<^sub>1 = (let ivs = map min_max (zip q\<^sub>0 q\<^sub>1) in (map fst ivs, map snd ivs))"

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

end
