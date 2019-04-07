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




fun partition :: "axis \<Rightarrow> real \<Rightarrow> point list \<Rightarrow> point list * point list * point list" where
  "partition _ _ [] = ([], [], [])"
| "partition a m (p # ps) = (
    let (lt, eq, gt) = partition a m ps in
    if p!a < m then (p # lt, eq, gt)
    else if p!a = m then (lt, p # eq, gt)
    else (lt, eq, p # gt)
  )"

definition partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "partition_by_median a ps = (
     let n = length ps div 2 in
     let ps' = map (\<lambda>p. p!a) ps in
     let m = sort ps' ! n in
     let (lt, eq, gt) = partition a m ps in
     let rem = n - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"

definition fast_partition_by_median :: "axis \<Rightarrow> point list \<Rightarrow> point list * real * point list" where
  "fast_partition_by_median a ps = (
     let n = length ps div 2 in
     let ps' = map (\<lambda>p. p!a) ps in
     let m = fast_select n ps' in
     let (lt, eq, gt) = partition a m ps in
     let rem = n - length lt in
     (lt @ take rem eq, m, drop rem eq @ gt)
  )"




lemma fast:
  "length ps > 0 \<Longrightarrow> fast_partition_by_median a ps = partition_by_median a ps"
  unfolding fast_partition_by_median_def partition_by_median_def
  by (auto simp del: fast_select.simps simp add: fast_select_correct select_def)

lemma partition_filter:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "lt = filter (\<lambda>p. p!a < m) ps"
    and "eq = filter (\<lambda>p. p!a = m) ps"
    and "gt = filter (\<lambda>p. p!a > m) ps"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_length:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "length ps = length lt + length eq + length gt"
    and "length lt + length eq = length (filter (\<lambda>p. p!a \<le> m) ps)"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_set:
  assumes "(lt, eq, gt) = partition a m ps"
  shows "set ps = set lt \<union> set eq \<union> set gt"
    and "set lt \<union> set eq = set (filter (\<lambda>p. p!a \<le> m) ps)"
  using assms by (induction ps arbitrary: lt eq gt) (auto split: prod.splits if_splits)

lemma partition_by_median_filter:
  assumes "(l, m, r) = partition_by_median a ps" "even (length ps)" "length ps > 0"
  shows partition_by_median_filter_l: "\<forall>p \<in> set l. p!a \<le> m"
    and partition_by_median_filter_r:  "\<forall>p \<in> set r. m \<le> p!a"
  using assms partition_filter
  apply (auto simp add: partition_by_median_def Let_def split: prod.splits)
  apply (smt in_set_takeD in_set_dropD mem_Collect_eq set_filter)+
  done

lemma partition_by_median_length_lr_0:
  assumes "(l, m, r) = partition_by_median a ps"
  shows "length ps = length l + length r"
  using assms partition_length
  apply (auto simp add: partition_by_median_def min_def Let_def split: prod.splits)
  apply (smt add.assoc)+
  done

lemma A:
  assumes "length lt + length eq > k" "length lt \<le> k"
  shows "length (lt @ take (k - length lt) eq) = k"
  using assms by simp

lemma C:
  "length (filter P xs) = length (filter P (sort xs))"
  by (simp add: filter_sort)

lemma A2:
  assumes "k < length xs" "sorted xs"
  shows "k < card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
proof -
  have "\<forall>i. i \<le> k \<longrightarrow> xs ! i \<le> xs ! k"
    using assms sorted_nth_mono by blast
  hence "{i. i \<le> k} \<subseteq> {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    using assms(1) by auto
  moreover have "finite {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    by simp
  ultimately have "card {i. i \<le> k} \<le> card {i. i < length xs \<and> xs ! i \<le> xs ! k}"
    using card_mono by blast
  thus ?thesis by simp
qed

lemma A1:
  assumes "k < length xs"
  shows "k < length (filter (\<lambda>x. x \<le> sort xs ! k) xs)"
proof -
  have "k < card {i. i < length (sort xs) \<and> sort xs ! i \<le> sort xs ! k}"
    using assms A2[of k "sort xs"] by simp
  also have "... = length (filter (\<lambda>x. x \<le> sort xs ! k) (sort xs))"
    using length_filter_conv_card[of "\<lambda>x. x \<le> sort xs ! k" "sort xs"] by simp
  also have "... = length (filter (\<lambda>x. x \<le> sort xs ! k) xs)"
    using C by metis
  finally show ?thesis .
qed

lemma B2:
  assumes "k < length xs" "sorted xs"
  shows "card {i. i < length xs \<and> xs ! i < xs ! k} \<le> k"
proof -
  have "\<forall>i. i < length xs \<and> xs!i < xs!k \<longrightarrow> i < k"
    using assms by (meson leD le_less_linear sorted_nth_mono)
  hence "{i. i < length xs \<and> xs ! i < xs ! k} \<subseteq> {i. i < k}"
    by blast
  hence "card {i. i < length xs \<and> xs ! i < xs ! k} \<le> card {i. i < k}"
    using card_mono by blast
  also have "... \<le> k"
    by simp
  finally show ?thesis .
qed

lemma B1:
  assumes "k < length xs"
  shows "length (filter (\<lambda>x. x < sort xs ! k) xs) \<le> k"
proof -
  have "length (filter (\<lambda>x. x < sort xs ! k) xs) = length (filter (\<lambda>x. x < sort xs ! k) (sort xs))"
    using C by blast
  also have "... = card {i. i < length (sort xs) \<and> sort xs ! i < sort xs ! k}"
    using length_filter_conv_card by blast
  also have "... \<le> k"
    using assms B2[of k "sort xs"] by simp
  finally show ?thesis .
qed

lemma D1:
  "length (filter (\<lambda>a. a < k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a < k) ps)"
  by (induction ps) auto

lemma D2:
  "length (filter (\<lambda>a. a \<le> k) (map (\<lambda>p. p!a) ps)) = length (filter (\<lambda>p. p!a \<le> k) ps)"
  by (induction ps) auto

lemma E:
  assumes "length l = length ps div 2" "length ps = length l + length r"
  shows "length r \<ge> length l" "length r - length l \<le> 1"
  using assms by simp_all

lemma partition_by_median_length_lr_1:
  assumes "(l, m, r) = partition_by_median a ps" "length ps > 0"
  shows "length r - length l \<le> 1" "length r \<ge> length l"
proof -

  let ?n = "length ps div 2"
  let ?ps' = "map (\<lambda>p. p!a) ps"
  let ?m = "sort ?ps' ! ?n"
  let ?leg = "partition a ?m ps"
  let ?lt = "fst ?leg"
  let ?eq = "fst (snd ?leg)"
  let ?gt = "snd (snd ?leg)"
  let ?rem = "?n - length ?lt"
  let ?l = "?lt @ take ?rem ?eq"
  let ?r = "drop ?rem ?eq @ ?gt"

  have "?n < length ?ps'"
    using assms(2) by auto
  hence "length (filter (\<lambda>a. a < ?m) ?ps') \<le> ?n" "length (filter (\<lambda>a. a \<le> ?m) ?ps') > ?n"
    using B1[of ?n ?ps'] A1[of ?n ?ps'] by auto
  hence LN: "length (filter (\<lambda>p. p!a < ?m) ps) \<le> ?n" "length (filter (\<lambda>p. p!a \<le> ?m) ps) > ?n"
    using D1[of ?m a ps] D2[of ?m a ps] by simp_all

  have "(?lt, ?eq, ?gt) = partition a ?m ps"
    by simp
  hence "?lt = filter (\<lambda>p. p!a < ?m) ps" "length ?lt + length ?eq = length (filter (\<lambda>p. p!a \<le> ?m) ps)"
    using partition_filter partition_length by fast+
  hence "length ?lt \<le> ?n" "length ?lt + length ?eq > ?n"
    using LN by simp_all
  hence X: "length ?l = ?n"
    using A by blast

  have Z: "(?l, ?m, ?r) = partition_by_median a ps"
    by (auto simp add: Let_def partition_by_median_def split: prod.splits)
  hence Y: "length ps = length ?l + length ?r"
    using assms partition_by_median_length_lr_0 by blast

  have "length ?r \<ge> length ?l" "length ?r - length ?l \<le> 1"
    using X Y E by blast+
  thus "length r - length l \<le> 1" "length r \<ge> length l" using Z by (metis Pair_inject assms(1))+
qed

lemma partition_by_median_length_lr_2:
  assumes "(l, m, r) = partition_by_median a ps" "even (length ps)" "length ps > 0"
  shows "length l = length r"
  using partition_by_median_length_lr_0 partition_by_median_length_lr_1 assms
  by (metis One_nat_def add.commute diff_is_0_eq even_diff_nat le_SucE le_antisym le_zero_eq odd_one)

lemma partition_by_median_length_lr_3: 
  assumes "(l, m, r) = partition_by_median a ps" "length ps > 1"
  shows "length l < length ps" and "length r < length ps"
  using assms partition_by_median_length_lr_1 partition_by_median_length_lr_2 partition_by_median_length_lr_0
  by (metis add_diff_cancel_left' gr0I less_trans zero_less_diff le_eq_less_or_eq add_diff_cancel_right' leD minus_nat.diff_0)+

lemmas partition_by_median_length = 
  partition_by_median_length_lr_0 partition_by_median_length_lr_1
  partition_by_median_length_lr_2 partition_by_median_length_lr_3

lemma partition_by_median_set:
  "(l, m, r) = partition_by_median a ps \<Longrightarrow> set ps = set l \<union> set r"
  using partition_set
  apply (auto simp add: Let_def partition_by_median_def split: prod.splits)
  apply (smt Un_iff UnCI in_set_takeD in_set_dropD append_take_drop_id set_append)+
  done

function (sequential) build' :: "axis \<Rightarrow> dimension \<Rightarrow> point list \<Rightarrow> kdt" where
  "build' a d [] = undefined"
| "build' a d [p] = Leaf p" 
| "build' a d ps = (
    let a' = (a + 1) mod d in
    let (l, m, r) = fast_partition_by_median a ps in
    Node a m (build' a' d l) (build' a' d r)
  )"
  by pat_completeness auto
termination build'
  using partition_by_median_length_lr_3
  apply (relation "measure (\<lambda>(a, d, ps). length ps)")
  apply (auto simp add: fast)
  apply fastforce+
  done

lemma build'_simp_1:
  "ps = [p] \<Longrightarrow> build' a d ps = Leaf p"
  by simp

lemma build'_simp_2:
  "ps = p\<^sub>0 # p\<^sub>1 # ps' \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = fast_partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'.simps(3) by (auto simp add: Let_def split: prod.splits)

lemma length_ps_gt_1:
  "length ps > 1 \<Longrightarrow> \<exists>p\<^sub>0 p\<^sub>1 ps'. ps = p\<^sub>0 # p\<^sub>1 # ps'"
  by (induction ps) (auto simp add: neq_Nil_conv)

lemma build'_simp_3:
  "length ps > 1 \<Longrightarrow> a' = (a + 1) mod d \<Longrightarrow> (l, m, r) = fast_partition_by_median a ps \<Longrightarrow> build' a d ps = Node a m (build' a' d l) (build' a' d r)"
  using build'_simp_2 length_ps_gt_1 by fast

lemmas build'_simps[simp] = build'_simp_1 build'_simp_2 build'_simp_3

declare build'.simps[simp del]

definition build :: "point list \<Rightarrow> kdt" where
  "build ps = build' 0 (dim (hd ps)) ps"




lemma pow2k_pow2k_1:
  assumes "x + y = 2 ^ k" "(x :: nat) = y" "k > 0"
  shows "x = 2 ^ (k - 1)"
    and "y = 2 ^ (k - 1)"
  using assms by (induction k) auto

lemma pow2k_eq_2pow2k_1: "k > 0 \<Longrightarrow> 2 * 2 ^ (k - 1) = 2 ^ k"
  by (cases k) auto

lemma pow2xy:
  "(2 :: nat) ^ x = 2 ^ y \<Longrightarrow> x = y"
  by simp

lemma build'_set:
  assumes "length ps = 2 ^ k"
  shows "set ps = set_kdt (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence E: "even (length ps)" "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    ultimately have "set ?l = set_kdt (build' ?a' d ?l)" "set ?r = set_kdt (build' ?a' d ?r)" 
      using "1.IH" by simp_all
    moreover have "set ps = set ?l \<union> set ?r"
      using partition_by_median_set fast E by (metis prod.collapse)
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis by auto
  qed
qed




lemma build'_invar:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "a < d"
  shows "invar d (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where P: "ps = [p]"
      using "1.prems" by (cases ps) auto
    hence "dim p = d"
      using "1.prems"(2) by simp
    thus ?thesis using P by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have A': "?a' < d"
      using "1.prems"(4) by auto

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence E: "even (length ps)" and P: "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence PLR: "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast E P by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    moreover have SPLR: "set ps = set ?l \<union> set ?r"
      using partition_by_median_set fast E P by (metis prod.collapse)
    moreover have "distinct ?l" "distinct ?r" and LR: "set ?l \<inter> set ?r = {}"
      using "1.prems"(3) SPLR PLR by (metis card_distinct distinct_append distinct_card length_append set_append)+
    moreover have "\<forall>p \<in> set ?l .dim p = d" "\<forall>p \<in> set ?r .dim p = d"
      using "1.prems"(2) SPLR by simp_all
    ultimately have "invar d (build' ?a' d ?l)" "invar d (build' ?a' d ?r)"
      using "1.IH" A' by simp_all
    moreover have "\<forall>p \<in> set ?l. p ! a \<le> ?m" "\<forall>p \<in> set ?r. ?m \<le> p ! a"
      using partition_by_median_filter E P fast by (metis prod.collapse)+
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using "1.prems"(4) LR L R build'_set by auto
  qed
qed





lemma size_height_kdt:
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
    using pow2k_eq_2pow2k_1 height_kdt_gt_0 by auto
  also have "... = 2 ^ (height_kdt (Node a d l r) - 1)"
    using Node by simp
  finally show ?case .
qed

lemma complete_size_height_kdt:
  assumes "complete_kdt kdt1" "complete_kdt kdt2" "size_kdt kdt1 = size_kdt kdt2"
  shows "height_kdt kdt1 = height_kdt kdt2"
proof -
  have "2 ^ (height_kdt kdt1 - 1) = 2 ^ (height_kdt kdt2 - 1)"
    using size_height_kdt assms by simp
  hence "height_kdt kdt1 - 1 = height_kdt kdt2 - 1"
    using pow2xy by blast
  thus ?thesis using height_kdt_gt_0
    by (metis One_nat_def Suc_pred)
qed

lemma build'_size:
  assumes "length ps = 2 ^ k"
  shows "size_kdt (build' a d ps) = length ps"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  then show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence E: "even (length ps)" "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence PLR: "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length E fast by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    ultimately have "size_kdt (build' ?a' d ?l) = length ?l" "size_kdt (build' ?a' d ?r) = length ?r" 
      using "1.IH" by simp_all
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using PLR by auto
  qed
qed




lemma build'_complete:
  assumes "length ps = 2 ^ k"
  shows "complete_kdt (build' a d ps)"
  using assms
proof (induction ps arbitrary: a k rule: length_induct)
  case (1 ps)
  show ?case
  proof (cases "length ps \<le> 1")
    case True
    then obtain p where "ps = [p]"
      using "1.prems" by (cases ps) auto
    thus ?thesis by simp
  next
    case False

    let ?a' = "(a + 1) mod d"
    let ?lmr = "fast_partition_by_median a ps"
    let ?l = "fst ?lmr"
    let ?m = "fst (snd ?lmr)"
    let ?r = "snd (snd ?lmr)"

    have K: "k > 0"
      using "1.prems" False gr0I by force
    hence "even (length ps)" "length ps > 0"
      using False "1.prems"(1) by simp_all
    hence PLR: "length ps = length ?l + length ?r" "length ?l = length ?r"
      using partition_by_median_length fast by (metis prod.collapse)+
    hence L: "length ?l = 2 ^ (k - 1)" and R: "length ?r = 2 ^ (k - 1)"
      using K "1.prems"(1) pow2k_pow2k_1 by simp_all
    moreover have "length ?l < length ps" "length ?r < length ps"
      using "1.prems"(1) K L R by simp_all
    ultimately have CL: "complete_kdt (build' ?a' d ?l)" and CR: "complete_kdt (build' ?a' d ?r)"
      using "1.IH" by simp_all

    have "size_kdt (build' ?a' d ?l) = length ?l" "size_kdt (build' ?a' d ?r) = length ?r"
      using build'_size L R by simp_all
    hence "size_kdt (build' ?a' d ?l) = size_kdt (build' ?a' d ?r)"
      using PLR(2) by simp
    hence "height_kdt (build' ?a' d ?l) = height_kdt (build' ?a' d ?r)"
      using CL CR complete_size_height_kdt by blast
    moreover have "build' a d ps = Node a ?m (build' ?a' d ?l) (build' ?a' d ?r)"
      using False by simp
    ultimately show ?thesis using CL CR by auto
  qed
qed



theorem build:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "set ps = set_kdt (build ps)"
    and "size_kdt (build ps) = length ps"
    and "complete_kdt (build ps)"
    and "invar d (build ps)"
  using assms build_def build'_set      apply simp
  using assms build_def build'_size     apply simp
  using assms build_def build'_complete apply simp
  using assms build_def build'_invar
  by (metis length_0_conv list.set_sel(1) power_not_zero zero_neq_numeral)

corollary build_height:
  assumes "length ps = 2 ^ k" "\<forall>p \<in> set ps. dim p = d" "distinct ps" "d > 0"
  shows "length ps = 2 ^ (height_kdt (build ps) - 1)"
  by (metis assms build(2,3) size_height_kdt)

end