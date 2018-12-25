theory Test
imports
  Main
begin

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

end