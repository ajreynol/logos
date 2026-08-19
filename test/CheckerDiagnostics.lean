import Cpc.Diagnostics

open Eo

private def diagnostic (proof : String) : String :=
  match parseProof proof with
  | .ok (assums, cmds) => logos_checker_failure_detail proof assums cmds
  | .error e => e

private def declarationsAndAssumptions : String :=
  "(declare-const x Int)
   (declare-const y Int)
   (assume @p0 (= y x))
   (assume @p1 (not (= x y)))"

-- A command that makes the checker stuck is identified by its source step ID.
#guard (diagnostic (declarationsAndAssumptions ++
    "(step @p2 :rule symm :premises ())
     (step @p3 :rule contra :premises (@p0 @p2))")).startsWith
  "Error: the checker became stuck at step @p2 (proof command 1):"

-- If no command gets stuck, report that it is the final refutation check that failed.
#guard diagnostic (declarationsAndAssumptions ++
    "(step @p2 :rule symm :premises (@p1))") ==
  "Error: every proof command executed without getting stuck, but the final state after step @p2 \
   is not a closed proof of false."
