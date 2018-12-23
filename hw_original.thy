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

(* **** *)

fun squared_distance :: "point \<Rightarrow> point \<Rightarrow> real" where
  "squared_distance [] [] = 0"
| "squared_distance (x # xs) (y # ys) = (x - y) ^ 2 + squared_distance xs ys"
| "squared_distance _ _ = undefined"

definition min_by_squared_distance :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "min_by_squared_distance p\<^sub>0 p\<^sub>1 q = (
    if squared_distance p\<^sub>0 q \<le> squared_distance p\<^sub>1 q then p\<^sub>0 else p\<^sub>1
  )"

fun nearest_neighbor' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> point" where
  "nearest_neighbor' _ _ _ Leaf = undefined"
| "nearest_neighbor' _ _ _ (Node Leaf p' Leaf) = p'"
| "nearest_neighbor' a k p (Node Leaf p' r) = (
    if p = p' \<or> p!a \<le> p'!a then
      p'
    else
      let candidate = nearest_neighbor' (incr a k) k p r in
      min_by_squared_distance candidate p' p
  )"
| "nearest_neighbor' a k p (Node l p' Leaf) = (
    if p = p' \<or> p!a > p'!a then
      p'
    else
      let candidate = nearest_neighbor' (incr a k) k p l in
      min_by_squared_distance candidate p' p
  )"
| "nearest_neighbor' a k p (Node l p' r) = (
    if p = p' then
      p
    else if p!a \<le> p'!a then
      let candidate = min_by_squared_distance p' (nearest_neighbor' (incr a k) k p l) p in
      if squared_distance p candidate > squared_distance p p' then
        let candidate' = nearest_neighbor' (incr a k) k p r in
        min_by_squared_distance candidate candidate' p
      else
        candidate
    else
      let candidate = min_by_squared_distance p' (nearest_neighbor' (incr a k) k p r) p in
      if squared_distance p candidate > squared_distance p p' then
        let candidate' = nearest_neighbor' (incr a k) k p l in
        min_by_squared_distance candidate candidate' p
      else
        candidate          
  )"

lemma nearest_neighbor'_in_kdt:
  assumes "invar' a k kdt" "dim p = k" "set_kdt kdt \<noteq> {}"
  shows "nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms
proof (induction a k p kdt rule: nearest_neighbor'.induct)
  case (1 a k n)
  thus ?case by simp
next
  case (2 a k p p')
  thus ?case by (simp add: isin_kdt')
next
  case (3 a k p p' rl rp' rr)
  thus ?case by (auto simp add: min_by_squared_distance_def Let_def)
next
  case (4 a k p ll lp' lr p')
  thus ?case by (auto simp add: min_by_squared_distance_def Let_def)
next
  case ("5_1" a k p ll lp' lr p' rl rp' rr)
  then show ?case sorry
next
  case ("5_2" a k p ll lp' lr p' rl rp' rr)
  then show ?case sorry
qed

lemma nearest_neighbor'_optimum:
  assumes "invar' a k kdt" "dim p = k" "set_kdt kdt \<noteq> {}"
  shows "\<forall>q \<in> set_kdt kdt. squared_distance (nearest_neighbor' a k p kdt) p \<le> squared_distance q p"
  using assms sorry

theorem nearest_neighbor':
  assumes "invar' a k kdt" "dim p = k" "set_kdt kdt \<noteq> {}"
  shows "(\<forall>q \<in> set_kdt kdt. squared_distance (nearest_neighbor' a k p kdt) p \<le> squared_distance q p) \<and> nearest_neighbor' a k p kdt \<in> set_kdt kdt"
  using assms nearest_neighbor'_in_kdt nearest_neighbor'_optimum by simp

(*
definition min_by_dim :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "min_by_dim d p\<^sub>0 p\<^sub>1 = (if p\<^sub>0!d \<le> p\<^sub>1!d then p\<^sub>0 else p\<^sub>1)"

fun find_min_kdt' :: "axis \<Rightarrow> dimension \<Rightarrow> dimension \<Rightarrow> kdt \<Rightarrow> point" where
  "find_min_kdt' _ _ _ Leaf = undefined"
| "find_min_kdt' a k d (Node Leaf p Leaf) = p"
| "find_min_kdt' a k d (Node Leaf p r   ) = (
    if a \<noteq> d then
      min_by_dim d p (find_min_kdt' (incr a k) k d r)
    else
      p
  )"
| "find_min_kdt' a k d (Node l    p Leaf) = min_by_dim d p (find_min_kdt' (incr a k) k d l)"
| "find_min_kdt' a k d (Node l    p r   ) = (
    let a' = incr a k in
    if a \<noteq> d then
      min_by_dim d p (min_by_dim d (find_min_kdt' a' k d l) (find_min_kdt' a' k d r))
    else
      min_by_dim d p (find_min_kdt' a' k d l)
  )"

lemma find_min_kdt':
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "\<forall>q \<in> set_kdt kdt. (find_min_kdt' a k d kdt)!d \<le> q!d"
  using assms
proof (induction kdt rule: find_min_kdt'.induct)
  case (1 a k d)
  thus ?case by simp
next
  case (2 a k d p)
  thus ?case by simp
next
  case (3 a k d p rl rp rr)
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  show ?case using 3
  proof (cases "a = d")
    case True
    hence "\<forall>q \<in> set_kdt ?r. p ! d < q ! d"
      using set_kdt_r_gt_a "3.prems"(1) by blast
    thus ?thesis using True 3 by (auto simp add: less_imp_le)
  next
    case False
    hence "\<forall>q \<in> set_kdt ?r. find_min_kdt' (incr a k) k d ?r ! d \<le> q ! d"
      using 3 by auto
    thus ?thesis using False 3 
      apply (auto simp add: min_by_dim_def)
      by (meson Un_iff order_trans)+
  qed
next
  case (4 a k d v va vb p)
  thus ?case 
    apply (auto simp add: min_by_dim_def)
    by (meson Un_iff order_trans)+
next
  case ("5_1" a k d ll lp lr p rl rp rr)
  let ?l = "\<langle>ll, lp, lr\<rangle>"
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  show ?case
  proof (cases "a = d")
    case True
    hence A: "\<forall>q \<in> set_kdt ?r. p ! d < q ! d"
      using "5_1.prems"(1) set_kdt_r_gt_a by blast
    have "\<forall>q \<in> set_kdt ?l. find_min_kdt' (incr a k) k d ?l ! d \<le> q ! d"
      using True "5_1.IH"(3) "5_1.prems"(1,3) by auto
    thus ?thesis using True A 
      apply (auto simp add: min_by_dim_def less_imp_le Let_def)
      by (meson Un_iff order_trans le_less_trans less_imp_le linear)+
  next
    case False
    hence A: "\<forall>q \<in> set_kdt ?l. find_min_kdt' (incr a k) k d ?l ! d \<le> q ! d"
      using "5_1.IH"(1) "5_1.prems"(1,3) by auto
    have "\<forall>q \<in> set_kdt ?r. find_min_kdt' (incr a k) k d ?r ! d \<le> q ! d"
      using False "5_1.IH"(2) "5_1.prems"(1,3) by auto
    thus ?thesis using False A 
      apply (auto simp add: min_by_dim_def Let_def)
      by (meson Un_iff order_trans le_less_trans less_imp_le linear)+
  qed
next
  case ("5_2" a k d ll lp lr p rl rp rr)
  let ?l = "\<langle>ll, lp, lr\<rangle>"
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  show ?case
  proof (cases "a = d")
    case True
    hence A: "\<forall>q \<in> set_kdt ?r. p ! d < q ! d"
      using "5_2.prems"(1) set_kdt_r_gt_a by blast
    have "\<forall>q \<in> set_kdt ?l. find_min_kdt' (incr a k) k d ?l ! d \<le> q ! d"
      using True "5_2.IH"(3) "5_2.prems"(1,3) by auto
    thus ?thesis using True A 
      apply (auto simp add: min_by_dim_def less_imp_le Let_def)
      by (meson Un_iff order_trans le_less_trans less_imp_le linear)+
  next
    case False
    hence A: "\<forall>q \<in> set_kdt ?l. find_min_kdt' (incr a k) k d ?l ! d \<le> q ! d"
      using "5_2.IH"(1) "5_2.prems"(1,3) by auto
    have "\<forall>q \<in> set_kdt ?r. find_min_kdt' (incr a k) k d ?r ! d \<le> q ! d"
      using False "5_2.IH"(2) "5_2.prems"(1,3) by auto
    thus ?thesis using False A 
      apply (auto simp add: min_by_dim_def Let_def)
      by (meson Un_iff order_trans le_less_trans less_imp_le linear)+
  qed
qed

definition max_by_dim :: "dimension \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point" where
  "max_by_dim d p\<^sub>0 p\<^sub>1 = (if p\<^sub>0!d \<ge> p\<^sub>1!d then p\<^sub>0 else p\<^sub>1)"

fun find_max_kdt' :: "axis \<Rightarrow> dimension \<Rightarrow> dimension \<Rightarrow> kdt \<Rightarrow> point" where
  "find_max_kdt' _ _ _ Leaf = undefined"
| "find_max_kdt' a k d (Node Leaf p Leaf) = p"
| "find_max_kdt' a k d (Node Leaf p r   ) = max_by_dim d p (find_max_kdt' (incr a k) k d r)"
| "find_max_kdt' a k d (Node l    p Leaf) = (
    if a \<noteq> d then
      max_by_dim d p (find_max_kdt' (incr a k) k d l)
    else
      p
  )"
| "find_max_kdt' a k d (Node l    p r   ) = (
    let a' = incr a k in
    if a \<noteq> d then
      max_by_dim d p (max_by_dim d (find_max_kdt' a' k d l) (find_max_kdt' a' k d r))
    else
      max_by_dim d p (find_max_kdt' a' k d r)
  )"

lemma find_max_kdt':
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "\<forall>q \<in> set_kdt kdt. (find_max_kdt' a k d kdt)!d \<ge> q!d"
  using assms
proof (induction kdt rule: find_max_kdt'.induct)
  case (1 a k d)
  thus ?case by simp
next
  case (2 a k d p)
  thus ?case by simp
next
  case (3 a k d p rl rp rr)
  thus ?case 
    apply (auto simp add: max_by_dim_def)
    by (meson Un_iff order_trans)+
next
  case (4 a k d ll lp lr p)
  thus ?case
    apply (auto simp add: max_by_dim_def)
    by (meson Un_iff order_trans)+
next
  case ("5_1" a k d ll lp lr p rl rp rr)
  let ?l = "\<langle>ll, lp, lr\<rangle>"
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  show ?case
  proof (cases "a = d")
    case True
    hence A: "\<forall>q \<in> set_kdt ?l. q ! a \<le> p ! a"
      using "5_1.prems"(1) set_kdt_l_lq_a  by blast
    have "\<forall> q \<in>set_kdt ?r. q ! d \<le> find_max_kdt' (incr a k) k d ?r ! d"
      using True "5_1.IH"(3) "5_1.prems"(1,3) by auto
    thus ?thesis using True A 
      apply (auto simp add: max_by_dim_def Let_def)
      by (meson Un_iff order.trans linear)+
  next
    case False
    hence A: "\<forall>q \<in> set_kdt ?l. q ! d \<le> find_max_kdt' (incr a k) k d ?l ! d"
      using "5_1.IH"(1) "5_1.prems"(1,3) by auto
    have "\<forall>q \<in> set_kdt ?r. q ! d \<le> find_max_kdt' (incr a k) k d ?r ! d"
      using False "5_1.IH"(2) "5_1.prems"(1,3) by auto
    thus ?thesis using False A 
      apply (auto simp add: max_by_dim_def Let_def)
      by (meson Un_iff order.trans linear)+
  qed
next
  case ("5_2" a k d ll lp lr p rl rp rr)
  let ?l = "\<langle>ll, lp, lr\<rangle>"
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  show ?case
  proof (cases "a = d")
    case True
    hence A: "\<forall>q \<in> set_kdt ?l. q ! a \<le> p ! a"
      using "5_2.prems"(1) set_kdt_l_lq_a  by blast
    have "\<forall> q \<in>set_kdt ?r. q ! d \<le> find_max_kdt' (incr a k) k d ?r ! d"
      using True "5_2.IH"(3) "5_2.prems"(1,3) by auto
    thus ?thesis using True A 
      apply (auto simp add: max_by_dim_def Let_def)
      by (meson Un_iff order.trans linear)+
  next
    case False
    hence A: "\<forall>q \<in> set_kdt ?l. q ! d \<le> find_max_kdt' (incr a k) k d ?l ! d"
      using "5_2.IH"(1) "5_2.prems"(1,3) by auto
    have "\<forall>q \<in> set_kdt ?r. q ! d \<le> find_max_kdt' (incr a k) k d ?r ! d"
      using False "5_2.IH"(2) "5_2.prems"(1,3) by auto
    thus ?thesis using False A 
      apply (auto simp add: max_by_dim_def Let_def)
      by (meson Un_iff order.trans linear)+
  qed
qed

fun del_kdt' :: "axis \<Rightarrow> dimension \<Rightarrow> point \<Rightarrow> kdt \<Rightarrow> kdt" where
  "del_kdt' _ _ _ Leaf = Leaf"
| "del_kdt' a k p (Node Leaf p' Leaf) = (
    if p = p' then
      Leaf
    else
      Node Leaf p' Leaf
  )"
| "del_kdt' a k p (Node Leaf p' r) = (
    if p = p' then
      let p'' = find_min_kdt' (incr a k) k a r in
      Node Leaf p'' (del_kdt' (incr a k) k p'' r)
    else if p!a > p'!a then
      Node Leaf p' (del_kdt' (incr a k) k p r)
    else
      Node Leaf p' r
  )"
| "del_kdt' a k p (Node l p' r) = (
    if p = p' then
      let p'' = find_max_kdt' (incr a k) k a l in
      Node (del_kdt' (incr a k) k p'' l) p'' r
    else if p!a > p'!a then
      Node l p' (del_kdt' (incr a k) k p r)
    else
      Node (del_kdt' (incr a k) k p l) p' r
  )"

lemma find_min_kdt'_in_kdt:
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "find_min_kdt' a k d kdt \<in> set_kdt kdt"
  using assms by (induction rule: find_min_kdt'.induct) (auto simp add: Let_def min_by_dim_def)

lemma invar'_dim:
  assumes "invar' a k kdt"
  shows "\<forall>p \<in> set_kdt kdt. dim p = k"
  using assms by(induction kdt arbitrary: a) (auto)

lemma find_min_kdt'_dim:
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "dim (find_min_kdt' a k d kdt) = k"
  using assms find_min_kdt'_in_kdt invar'_dim by blast

lemma find_max_kdt'_in_kdt:
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "find_max_kdt' a k d kdt \<in> set_kdt kdt"
  using assms by (induction kdt rule: find_max_kdt'.induct) (auto simp add: Let_def max_by_dim_def)

lemma find_max_kdt'_dim:
  assumes "invar' a k kdt" "set_kdt kdt \<noteq> {}" "d < k"
  shows "dim (find_max_kdt' a k d kdt) = k"
  using assms find_max_kdt'_in_kdt invar'_dim by auto

lemma incr_a_k_l_k[simp]:
  "k > 0 \<Longrightarrow> incr a k < k"
  by auto

lemma set_del_kdt':
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "set_kdt (del_kdt' a k p kdt) = set_kdt kdt - {p}"
  using assms
proof (induction rule: del_kdt'.induct)
  case (1 a k p)
  thus ?case by simp
next
  case (2 a k p p')
  thus ?case by simp
next
  case (3 a k p p' rl rp' rr)
  consider (A) "p = p'" | (B) "p \<noteq> p' \<and> p!a \<le> p'!a" | (C) "p \<noteq> p' \<and> p!a > p'!a"
    by force
  then show ?case
  proof cases
    case A
    let ?r = "\<langle>rl, rp', rr\<rangle>"
    let ?p'' = "find_min_kdt' (incr a k) k a ?r"

    have ID: "invar' (incr a k) k ?r \<and> dim ?p'' = k"
      using A 3 find_min_kdt'_dim by simp
    hence IH: "set_kdt (del_kdt' (incr a k) k ?p'' ?r) = set_kdt ?r - {?p''}"
      using A 3 by (meson incr_a_k_l_k invar'_dim_gt_0)

    have P: "p \<notin> set_kdt ?r"
      using "3.prems"(1) A set_kdt_r_gt_a by blast
    have P'': "?p'' \<in> set_kdt ?r"
      by (metis "3.prems"(3) Un_empty ID find_min_kdt'_in_kdt insert_not_empty set_kdt.simps(2))

    have "set_kdt (del_kdt' a k p \<langle>\<langle>\<rangle>, p', ?r\<rangle>) = set_kdt \<langle>\<langle>\<rangle>, ?p'', (del_kdt' (incr a k) k ?p'' ?r)\<rangle>"
      using A by (metis del_kdt'.simps(3))
    also have "... = set_kdt \<langle>\<rangle> \<union> {?p''} \<union> set_kdt (del_kdt' (incr a k) k ?p'' ?r)"
      by simp
    also have "... = set_kdt ?r"
      using P'' IH by auto
    also have "... = set_kdt ?r \<union> {p'} - {p}"
      using A P by blast
    also have "... = set_kdt \<langle>\<langle>\<rangle>, p', \<langle>rl, rp', rr\<rangle>\<rangle> - {p}"
      by force
    finally show ?thesis .
  next
    case B
    hence "p \<notin> set_kdt \<langle>rl, rp', rr\<rangle>"
      by (smt "3.prems"(1) set_kdt_r_gt_a)
    then show ?thesis using B 3 by simp
  next
    case C
    then show ?thesis using 3 by auto
  qed
next
  case ("4_1" a k p ll lp' lr p' r)
  let ?l = "\<langle>ll, lp', lr\<rangle>"
  consider (A) "p = p'" | (B) "p \<noteq> p' \<and> p!a \<le> p'!a" | (C) "p \<noteq> p' \<and> p!a > p'!a"
    by force
  then show ?case
  proof cases
    case A
    let ?p'' = "find_max_kdt' (incr a k) k a ?l"
    have IH: "set_kdt (del_kdt' (incr a k) k ?p'' ?l) = set_kdt ?l - {?p''}"
      using A by (metis "4_1.IH"(1) "4_1.prems"(1,3) Un_empty_right Un_iff find_max_kdt'_dim incr_a_k_l_k invar'.simps(2) isin_kdt' isin_kdt'.simps(2) le_less_trans mk_disjoint_insert zero_le)

    have P: "p \<notin> set_kdt ?l \<and> p \<notin> set_kdt r"
      using "4_1.prems"(1) A invar'.simps(2) by blast
    have P'': "?p'' \<in> set_kdt ?l"
      by (metis "4_1.prems"(1) "4_1.prems"(3) Un_empty find_max_kdt'_in_kdt insert_not_empty invar'.simps(2) set_kdt.simps(2))

    have "set_kdt (del_kdt' a k p \<langle>?l, p', r\<rangle>) = set_kdt \<langle>(del_kdt' (incr a k) k ?p'' ?l), ?p'', r\<rangle>"
      using A "4_1" by (metis del_kdt'.simps(4))
    also have "... = set_kdt (del_kdt' (incr a k) k ?p'' ?l) \<union> {?p''} \<union> set_kdt r"
      by simp
    also have "... = (set_kdt ?l - {?p''}) \<union> {?p''} \<union> set_kdt r"
      using IH by blast
    also have "... = set_kdt ?l \<union> {p'} \<union> set_kdt r - {p}"
      using A P P'' by blast
    also have "... = set_kdt \<langle>?l, p', r\<rangle> - {p}"
      using A by auto
    finally show ?thesis .
  next
    case B
    hence IH: "set_kdt (del_kdt' (incr a k) k p ?l) = set_kdt ?l - {p}"
      using "4_1.prems" "4_1.IH"(3) invar'_dim_gt_0 incr_a_k_l_k by (metis invar'.simps(2) le_less_trans less_irrefl)
    have P: "p \<notin> set_kdt r"
      using B "4_1" by (meson leD set_kdt_r_gt_a)

    have "set_kdt (del_kdt' a k p \<langle>?l, p', r\<rangle>) = set_kdt \<langle>(del_kdt' (incr a k) k p ?l), p', r\<rangle>"
      using B by simp
    also have "... = set_kdt (del_kdt' (incr a k) k p ?l) \<union> {p'} \<union> set_kdt r"
      by simp
    also have "... = (set_kdt ?l - {p}) \<union> {p'} \<union> set_kdt r"
      using IH by simp
    also have "... = set_kdt ?l \<union> {p'} \<union> set_kdt r - {p}"
      using B P by blast
    also have "... = set_kdt \<langle>?l, p', r\<rangle> - {p}"
      using B by force
    finally show ?thesis .
  next
    case C
    hence IH: "set_kdt (del_kdt' (incr a k) k p r) = set_kdt r - {p}"
      using "4_1" by (meson incr_a_k_l_k invar'.simps(2) invar'_dim_gt_0)

    have P: "p \<notin> set_kdt ?l"
      using C by (smt "4_1.prems"(1) set_kdt_l_lq_a)

    have "set_kdt (del_kdt' a k p \<langle>?l, p', r\<rangle>) = set_kdt \<langle>?l, p', (del_kdt' (incr a k) k p r)\<rangle>"
      using "4_1" C del_kdt'.simps(4) by presburger
    also have "... = set_kdt ?l \<union> {p'} \<union> set_kdt (del_kdt' (incr a k) k p r)"
      by auto
    also have "... = set_kdt ?l \<union> {p'} \<union> (set_kdt r - {p})"
      using IH by auto
    also have "... = set_kdt ?l \<union> {p'} \<union> set_kdt r - {p}"
      using C P by blast
    also have "... = set_kdt \<langle>?l, p', r\<rangle> - {p}"
      by force
    finally show ?thesis .
  qed
next
  case ("4_2" a k p ll lp' lr p' rl rp' rr)
  then show ?case sorry
qed

lemma invar_del_kdt': 
  assumes "invar' a k kdt" "dim p = k" "a < k"
  shows "invar' a k (del_kdt' a k p kdt)"
  using assms
proof (induction kdt rule: del_kdt'.induct)
  case (1 a k p)
  thus ?case by simp
next
  case (2 a k p p')
  thus ?case by simp
next
  case (3 a k p p' rl rp rr)
  let ?r = "\<langle>rl, rp, rr\<rangle>"
  consider (A) "p = p'" | (B) "p \<noteq> p' \<and> p!a \<le> p'!a" | (C) "p \<noteq> p' \<and> p!a > p'!a"
    by force
  thus ?case
  proof cases
    case A
    let ?p'' = "find_min_kdt' (incr a k) k a ?r"
    have ID: "invar' (incr a k) k ?r \<and> dim ?p'' = k"
      using A 3 by (metis empty_not_insert find_min_kdt'_dim insert_absorb invar'.simps(2) isin_kdt' isin_kdt'.simps(2))

    have IH: "invar' (incr a k) k (del_kdt' (incr a k) k ?p'' ?r) \<and> invar' (incr a k) k \<langle>\<rangle>"
      using 3 A ID incr_a_k_l_k invar'_dim_gt_0 by (meson invar'.simps(1))

    have P'': "set_kdt (del_kdt' (incr a k) k ?p'' ?r) = set_kdt ?r - {?p''}"                     
      using 3 A set_del_kdt' by (smt Diff_insert_absorb ID Un_empty find_min_kdt'_in_kdt incr_a_k_l_k insert_not_empty invar'_dim_gt_0 mk_disjoint_insert set_kdt.simps(2))

    have "\<forall>q \<in> set_kdt ?r. ?p''!a \<le> q!a"
      using find_min_kdt' "3.prems"(3) Diff_empty ID by blast
    hence X: "\<forall>q \<in> set_kdt (del_kdt' (incr a k) k ?p'' ?r). ?p''!a \<le> q!a"
      using P'' by blast

    have "del_kdt' a k p \<langle>\<langle>\<rangle>, p', ?r\<rangle> = \<langle>\<langle>\<rangle>, ?p'', (del_kdt' (incr a k) k ?p'' ?r)\<rangle>"
      using A by (meson del_kdt'.simps(3))
    then show ?thesis using ID IH A 3 P'' X sorry
  next
    case B
    then show ?thesis using 3 by auto
  next
    case C
    hence A: "invar' (incr a k) k (del_kdt' (incr a k) k p \<langle>rl, rp, rr\<rangle>)" using 3 by simp
    have B: "invar' (incr a k) k Leaf" using 3 by auto
    have X: "dim p' = k \<and> (\<forall>q \<in> set_kdt Leaf. \<exists>i < k. q!i \<noteq> p'!i)" using 3 by simp
    have D: "\<forall>q \<in> set_kdt Leaf. q!a \<le> p'!a" by simp
    have "set_kdt (del_kdt' (incr a k) k p \<langle>rl, rp, rr\<rangle>) = set_kdt \<langle>rl, rp, rr\<rangle> - {p}"
      using "3.prems"(1) "3.prems"(2) set_del_kdt' by auto
    hence E: "\<forall>q \<in> set_kdt (del_kdt' (incr a k) k p \<langle>rl, rp, rr\<rangle>). q!a > p'!a" using 3
      by (metis DiffD1 invar'.simps(2))
    then show ?thesis using A B X D E
      by (simp add: C)
  qed
next
  case ("4_1" a k p v va vb p' r)
  then show ?case sorry
next
  case ("4_2" a k p vc vd ve p' v va vb)
  then show ?case sorry
qed

*)




  

end
