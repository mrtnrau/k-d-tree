theory Balanced
imports
  Complex_Main 
  "KDTree"
  "Median_Of_Medians_Selection.Median_Of_Medians_Selection"
begin

text \<open>
  Widest spread axis of a list of points.
\<close>

definition spread :: "axis \<Rightarrow> point set \<Rightarrow> real" where
  "spread a ps = (
    let as = (\<lambda>p. p!a) ` ps in
    Max as - Min as
  )"

definition is_widest_spread :: "axis \<Rightarrow> dimension \<Rightarrow> point set \<Rightarrow> bool" where
  "is_widest_spread a k ps = (\<forall>a' < k. spread a' ps \<le> spread a ps)"

fun widest_spread' :: "axis \<Rightarrow> point list \<Rightarrow> axis * real" where
  "widest_spread' 0 ps = (0, spread 0 (set ps))"
| "widest_spread' a ps = (
    let (a', s') = widest_spread' (a - 1) ps in
    let s = spread a (set ps) in
    if s \<le> s' then (a', s') else (a, s)
  )"

fun widest_spread :: "point list \<Rightarrow> axis" where
  "widest_spread [] = undefined"
| "widest_spread (p # ps) = (
    let (a, _) = widest_spread' (dim p - 1) (p # ps) in
    a
  )"

fun widest_spread_invar :: "dimension \<Rightarrow> kdt \<Rightarrow> bool" where
  "widest_spread_invar _ (Leaf _) \<longleftrightarrow> True"
| "widest_spread_invar k (Node a s l r) \<longleftrightarrow> is_widest_spread a k (set_kdt l \<union> set_kdt r) \<and> widest_spread_invar k l \<and> widest_spread_invar k r"

lemma widest_spread'_is_spread:
  "(ws, s) = widest_spread' a ps \<Longrightarrow> s = spread ws (set ps)"
  by (induction a) (auto simp add: Let_def split: prod.splits if_splits)

lemma is_widest_spread_k_le_ws:
  "is_widest_spread ws k ps \<Longrightarrow> spread k ps \<le> spread ws ps \<Longrightarrow> is_widest_spread ws (k+1) ps"
  using is_widest_spread_def less_Suc_eq by auto

lemma is_widest_spread_k_gt_ws:
  "is_widest_spread ws k ps \<Longrightarrow> \<not> (spread k ps \<le> spread ws ps) \<Longrightarrow> is_widest_spread k (k+1) ps"
  using is_widest_spread_def less_Suc_eq by auto

lemma widest_spread'_is_widest_spread:
  "(ws, s) = widest_spread' a ps \<Longrightarrow> is_widest_spread ws (a+1) (set ps)"
proof (induction a arbitrary: ws s)
  case 0
  thus ?case
    using is_widest_spread_def by simp
next
  case (Suc a)
  then obtain ws' s' where *: "(ws', s') = widest_spread' a ps"
    by (metis surj_pair)
  hence "is_widest_spread ws' (Suc a) (set ps)"
    using Suc.IH by simp
  then show ?case 
    using Suc.prems * widest_spread'_is_spread is_widest_spread_k_le_ws[of ws' "Suc a" "set ps"] is_widest_spread_k_gt_ws[of ws' "Suc a" "set ps"]
    by (auto simp add: Let_def split: prod.splits if_splits)
qed

lemma widest_spread_is_widest_spread:
  assumes "ps \<noteq> []" "\<forall>p \<in> set ps. dim p = k" "0 < k"
  shows "is_widest_spread (widest_spread ps) k (set ps)"
proof (cases ps)
  case Nil
  thus ?thesis
    using assms(1) by simp
next
  case (Cons p ps)
  obtain ws s where *: "(ws, s) = widest_spread' (dim p - 1) (p # ps)"
    using prod.collapse by blast
  moreover have "dim p = k"
    using Cons assms(2) by simp
  ultimately have "is_widest_spread ws (k - 1 + 1) (set (p # ps))"
    using widest_spread'_is_widest_spread by blast
  thus ?thesis
    using Cons * assms(3) by (auto split: prod.split)
qed




text \<open>
  Finding the median of points wrt axis a.
\<close>

definition axis_median :: "axis \<Rightarrow> point list \<Rightarrow> real" where
  "axis_median a ps = (
    let n = (length ps - 1) div 2  in
    let ps' = map (\<lambda>p. p!a) ps in
    fast_select n ps'
  )"

lemma size_mset_map_P:
  "size {# y \<in># mset (map f xs). P y #} = size {# x \<in># mset xs. P (f x) #}"
  by (induction xs) auto

lemma size_axis_median_length:
  assumes "0 < length ps"
  shows "size {# p \<in># mset ps. p!a < axis_median a ps #} \<le> (length ps - 1) div 2" (is "?thesis1")
    and "size {# p \<in># mset ps. axis_median a ps < p!a #} \<le> length ps div 2"       (is "?thesis2")
proof -
  let ?n = "(length ps - 1) div 2"
  let ?ps' = "map (\<lambda>p. p!a) ps"
  let ?m = "fast_select ?n ?ps'"

  have "length ps = length ?ps'"
    by simp
  moreover have "?n < length ?ps'"
    using assms calculation by linarith
  ultimately have *: "median ?ps' = ?m"
    using median_def fast_select_correct by metis

  have "size {# a \<in># mset ?ps'. a < ?m #} \<le> (length ps - 1) div 2"
    using * size_less_than_median[of ?ps'] by simp
  hence "size {# p \<in># mset ps. p!a < ?m #} \<le> (length ps - 1) div 2"
    using size_mset_map_P[of "\<lambda>a. a < ?m"] by metis
  thus ?thesis1
    using axis_median_def by metis
  
  have "size {# a \<in># mset ?ps'. ?m < a #} \<le> length ps div 2"
    using * size_greater_than_median[of ?ps'] by simp
  hence "size {# p \<in># mset ps. ?m < p!a #} \<le> length ps div 2"
    using size_mset_map_P[of "\<lambda>a. ?m < a"] by metis
  thus ?thesis2 
    using axis_median_def by metis
qed




text \<open>
  Partitioning points by axis < = > to some value m.
\<close>

fun partition :: "axis \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point list * point list * point list" where
  "partition _ _ [] = ([], [], [])"
| "partition a m (p # ps) = (
    let (lt, eq, gt) = partition a m ps in
    if p!a < m then 
      (p # lt, eq, gt)
    else if p!a = m then 
      (lt, p # eq, gt)
    else 
      (lt, eq, p # gt)
  )"

lemma partition_set:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "set ps = set lt \<union> set eq \<union> set gt"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_mset:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "mset lt = {# p \<in># mset ps. p!a < m #}"
    and "mset eq = {# p \<in># mset ps. p!a = m #}"
    and "mset gt = {# p \<in># mset ps. m < p!a #}"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_filter:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "\<forall>p \<in> set lt. p!a < m"
    and "\<forall>p \<in> set eq. p!a = m"
    and "\<forall>p \<in> set gt. m < p!a"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_length:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "length ps = length lt + length eq + length gt"
    and "length lt = size {# p \<in># mset ps. p!a < m #}"
    and "length eq = size {# p \<in># mset ps. p!a = m #}"
    and "length gt = size {# p \<in># mset ps. m < p!a #}"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)




text \<open>
  Partitioning points balanced wrt the median at axis a.
\<close>

definition partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "partition_by_median a ps = (
     let m = axis_median a ps in
     let (lt, eq, gt) = partition a m ps in
     let rem = length ps div 2 - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"

lemma partition_by_median_set:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "set ps = set l \<union> set r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def split: prod.splits)
  by (smt partition_set append_take_drop_id set_append inf_sup_aci(6))

lemma partition_by_median_filter:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "\<forall>p \<in> set l. p!a \<le> m"
    and "\<forall>p \<in> set r. m \<le> p!a"
  using assms unfolding partition_by_median_def
  apply (auto simp add: Let_def split: prod.splits)
  by (smt partition_filter in_set_takeD in_set_dropD)+

lemma partition_by_median_length_1:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "length ps = length l + length r"
  using assms unfolding partition_by_median_def
  apply (simp add: Let_def min_def split: prod.splits)
  by (smt partition_length add.assoc)

lemma partition_by_median_length_2:
  assumes "(l, m, r) = partition_by_median a ps" "0 < length ps"
  shows "length r - length l \<le> 1"
    and "length l \<le> length r"
proof -
  let ?m = "axis_median a ps"
  let ?leg = "partition a ?m ps"
  let ?lt = "fst ?leg"
  let ?eq = "fst (snd ?leg)"
  let ?gt = "snd (snd ?leg)"
  let ?rem = "length ps div 2 - length ?lt"
  let ?l = "?lt @ take ?rem ?eq"
  let ?r = "drop ?rem ?eq @ ?gt"

  have *: "(?lt, ?eq, ?gt) = partition a ?m ps"
    by simp
  have "length ?lt \<le> (length ps - 1) div 2"
    using assms * partition_length(2) size_axis_median_length(1) by presburger
  moreover have "length ?gt \<le> length ps div 2"
    using assms * partition_length(4) size_axis_median_length(2) by presburger
  moreover have "length ps = length ?lt + length ?eq + length ?gt"
    using * partition_length(1) by simp
  ultimately have L: "length ?l = length ps div 2"
    by simp

  have **: "(?l, ?m, ?r) = partition_by_median a ps"
    by (auto simp add: Let_def partition_by_median_def split: prod.splits)
  hence "length ps = length ?l + length ?r"
    using partition_by_median_length_1 by blast
  hence "length ?l \<le> length ?r" "length ?r - length ?l \<le> 1"
    using L by linarith+

  thus "length l \<le> length r" "length r - length l \<le> 1" 
    using ** by (metis Pair_inject assms(1))+
qed

lemma partition_by_median_length_3: 
  assumes "(l, m, r) = partition_by_median a ps" "0 < length ps"
  shows "length l < length ps"
proof (rule ccontr)
  assume *: "\<not> (length l < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length l = length ps" "length r = 0"
    using * by simp_all
  moreover have "length l \<le> length r"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_4: 
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "length r < length ps"
proof (rule ccontr)
  assume *: "\<not> (length r < length ps)"
  have "length ps = length l + length r"
    using partition_by_median_length_1 assms(1) by simp
  hence "length r = length ps" "length l = 0"
    using * by simp_all
  moreover have "length r - length l \<le> 1"
    using partition_by_median_length_2 assms by fastforce+
  ultimately show "False" using assms(2) by simp
qed

lemma partition_by_median_length_5:
  assumes "(l, m, r) = partition_by_median a ps" "1 < length ps"
  shows "0 < length l"
    and "0 < length r"
  using assms partition_by_median_length_1 partition_by_median_length_4 apply simp
  using assms partition_by_median_length_1 partition_by_median_length_3 by fastforce

lemmas partition_by_median_length = 
  partition_by_median_length_1 partition_by_median_length_2
  partition_by_median_length_3 partition_by_median_length_4
  partition_by_median_length_5




text \<open>
  The build algorithm.

  At each level splits the point into two lists depending on the median at the particular axis a.
  The left list contains points with p!a <= median at axis a.
  The right list contains points with median at axis a <= p!a.
  The two lists differ in length by at most 1.
\<close>

function (sequential) build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a k [] = undefined" (* We never hit this case recursively. Only if the original input is really [].*)
| "build' a k [p] = Leaf p" 
| "build' a k ps = (
    let a' = (a + 1) mod k in
    let (l, m, r) = partition_by_median a ps in
    Node a m (build' a' k l) (build' a' k r)
  )"
  by pat_completeness auto
termination build'
  using partition_by_median_length(4,5)
  apply (relation "measure (\<lambda>(_, _, ps). length ps)")
  apply (auto)
  apply fastforce+
  done




text \<open>
  Setting up different build.simps for length_induct.
\<close>

lemma build'_simp_1:
  "ps = [p] \<Longrightarrow> build' a k ps = Leaf p"
  by simp

lemma build'_simp_2:
  "ps = p\<^sub>0 # p\<^sub>1 # ps' \<Longrightarrow> a' = (a + 1) mod k \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build' a k ps = Node a m (build' a' k l) (build' a' k r)"
  using build'.simps(3) by (auto simp add: Let_def split: prod.splits)

lemma length_ps_gt_1:
  "1 < length ps \<Longrightarrow> \<exists>p\<^sub>0 p\<^sub>1 ps'. ps = p\<^sub>0 # p\<^sub>1 # ps'"
  by (induction ps) (auto simp add: neq_Nil_conv)

lemma build'_simp_3:
  "1 < length ps \<Longrightarrow> a' = (a + 1) mod k \<Longrightarrow> (l, m, r) = partition_by_median a ps \<Longrightarrow> build' a k ps = Node a m (build' a' k l) (build' a' k r)"
  using build'_simp_2 length_ps_gt_1 by fast

lemmas build'_simps[simp] = build'_simp_1 build'_simp_3

declare build'.simps[simp del]




text \<open>
  The main lemmas.
\<close>

lemma build'_set:
  assumes "0 < length ps"
  shows "set ps = set_kdt (build' a k ps)"
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

    let ?a' = "(a + 1) mod k"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have "set ?l = set_kdt (build' ?a' k ?l)" "set ?r = set_kdt (build' ?a' k ?r)" 
      using False partition_by_median_length(4,5,6,7)[of ?l ?m ?r a ps] "1.IH" by force+
    moreover have "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "build' a k ps = Node a ?m (build' ?a' k ?l) (build' ?a' k ?r)"
      using False by simp
    ultimately show ?thesis
      by auto
  qed
qed

lemma build'_invar:
  assumes "0 < length ps" "\<forall>p \<in> set ps. dim p = k" "distinct ps" "a < k"
  shows "invar k (build' a k ps)"
  using assms
proof (induction ps arbitrary: a rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where P: "ps = [p]"
      using "1.prems" by (cases ps) auto
    hence "dim p = k"
      using "1.prems"(2) by simp
    thus ?thesis using P by simp
  next
    case False

    let ?a' = "(a + 1) mod k"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 0: "?a' < k"
      using "1.prems"(4) by auto
    have 1: "length ps = length ?l + length ?r"
      using partition_by_median_length by (metis prod.collapse)+
    hence 2: "length ?l < length ps" "length ?r < length ps"
      using False partition_by_median_length(4,5) not_le_imp_less "1.prems" by (smt prod.collapse)+
    hence 3: "0 < length ?l" "0 < length ?r"
      using 1 False partition_by_median_length(6,7) by simp_all
    moreover have SPLR: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set by (metis prod.collapse)
    moreover have "distinct ?l" "distinct ?r" and 4: "set ?l \<inter> set ?r = {}"
      using "1.prems"(3) SPLR 1 by (metis card_distinct distinct_append distinct_card length_append set_append)+
    moreover have "\<forall>p \<in> set ?l .dim p = k" "\<forall>p \<in> set ?r .dim p = k"
      using "1.prems"(2) SPLR by simp_all
    ultimately have "invar k (build' ?a' k ?l)" "invar k (build' ?a' k ?r)"
      using "1.IH" 0 2 by simp_all
    moreover have "\<forall>p \<in> set ?l. p ! a \<le> ?m" "\<forall>p \<in> set ?r. ?m \<le> p ! a"
      using partition_by_median_filter by (metis prod.collapse)+
    moreover have "build' a k ps = Node a ?m (build' ?a' k ?l) (build' ?a' k ?r)"
      using False by simp
    ultimately show ?thesis 
      using "1.prems"(4) 3 4 build'_set by auto
  qed
qed

lemma build'_size:
  assumes "0 < length ps"
  shows "size_kdt (build' a k ps) = length ps"
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

    let ?a' = "(a + 1) mod k"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have "size_kdt (build' ?a' k ?l) = length ?l" "size_kdt (build' ?a' k ?r) = length ?r" 
      using False partition_by_median_length(4,5,6,7)[of ?l ?m ?r a ps] "1.IH" by force+
    moreover have "build' a k ps = Node a ?m (build' ?a' k ?l) (build' ?a' k ?r)"
      using False by simp
    ultimately show ?thesis
      using partition_by_median_length(1) by (smt prod.collapse size_kdt.simps(2))
  qed
qed

lemma build'_balanced:
  assumes "0 < length ps"
  shows "balanced (build' a k ps)"
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

    let ?a' = "(a + 1) mod k"
    let ?lmr = "partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have 0: "length ps = length ?l + length ?r" "length ?r - length ?l \<le> 1" "length ?l \<le> length ?r"
      using partition_by_median_length(1,2,3) "1.prems" by (metis prod.collapse)+
    hence 1: "length ?l + 1 = length ?r \<or> length ?l = length ?r"
      by linarith
    moreover have 2: "length ?l < length ps" "length ?r < length ps"
      using False 0 by auto
    moreover have 3: "0 < length ?l" "0 < length ?r"
      using "1.prems" 0 1 2 by linarith+
    ultimately have 4: "balanced (build' ?a' k ?l)" "balanced (build' ?a' k ?r)"
      using "1.IH" by simp_all
    have "build' a k ps = Node a ?m (build' ?a' k ?l) (build' ?a' k ?r)"
      using False by simp
    moreover have "size_kdt (build' ?a' k ?l) + 1 = size_kdt (build' ?a' k ?r) \<or> size_kdt (build' ?a' k ?l) = size_kdt (build' ?a' k ?r)"
      using 1 3 build'_size by simp
    ultimately show ?thesis
      using 4 balanced_Node_if_wbal2 by auto
  qed
qed

lemma complete_if_balanced_size_2powh:
  assumes "balanced kdt" "size_kdt kdt = 2 ^ h"
  shows "complete kdt"
proof (rule ccontr)
  assume "\<not> complete kdt"
  hence "2 ^ (min_height kdt) < size_kdt kdt" "size_kdt kdt < 2 ^ height kdt"
    by (simp_all add: min_height_size_if_incomplete size_height_if_incomplete)
  hence "height kdt - min_height kdt > 1"
    using assms(2) by simp
  hence "\<not> balanced kdt"
    using balanced_def by simp
  thus "False"
    using assms(1) by simp
qed

lemma build'_complete:
  assumes "length ps = 2 ^ h"
  shows "complete (build' a k ps)"
  using assms complete_if_balanced_size_2powh
  by (simp add: build'_balanced build'_size)




text \<open>
  Wrapping up with the final build function.
\<close>

definition build :: "point list \<Rightarrow> kdt" where
  "build ps = build' 0 (dim (hd ps)) ps"

theorem build_set:
  "0 < length ps \<Longrightarrow> set ps = set_kdt (build ps)"
  using build'_set build_def by simp

theorem build_invar:
  "0 < length ps \<Longrightarrow> \<forall>p \<in> set ps. dim p = k \<Longrightarrow> distinct ps \<Longrightarrow> 0 < k \<Longrightarrow> invar k (build ps)"
  using build'_invar build_def by simp

theorem build_size:
  "0 < length ps \<Longrightarrow> length ps = size_kdt (build ps)"
  using build'_size build_def by simp

theorem build_balanced:
  "0 < length ps \<Longrightarrow> balanced (build ps)"
  using build'_balanced build_def by simp

theorem build_complete:
  "length ps = 2 ^ h \<Longrightarrow> complete (build ps)"
  using build'_complete build_def by simp

theorem build_height:
  "length ps = 2 ^ h \<Longrightarrow> length ps = 2 ^ (height (build ps))"
  using build_complete build_size complete_iff_size by auto

end