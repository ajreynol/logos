import CpcMini.SmtModel

open SmtEval

namespace Smtm

/-! Proof-only legacy predicate retained outside `SmtModel`.

`__smtx_type_wf` no longer uses this scoped no-alias check; it now uses
`__smtx_type_names_consistent`. Some Mini proofs still mention the old structural
predicate while they are migrated to the new consistency facts.
-/
mutual
def __smtx_dt_cons_no_alias_rec (refs : RefList) : SmtDatatypeCons -> native_Bool
  | SmtDatatypeCons.cons T c =>
      native_ite (__smtx_type_no_alias_rec refs T) (__smtx_dt_cons_no_alias_rec refs c) false
  | SmtDatatypeCons.unit => true

def __smtx_dt_no_alias_rec (refs : RefList) : SmtDatatype -> native_Bool
  | SmtDatatype.null => true
  | SmtDatatype.sum c d =>
      native_ite (__smtx_dt_cons_no_alias_rec refs c) (__smtx_dt_no_alias_rec refs d) false

def __smtx_type_no_alias_rec : RefList -> SmtType -> native_Bool
  | refs, SmtType.Datatype s d =>
      native_ite (native_reflist_contains refs s) false
        (__smtx_dt_no_alias_rec (native_reflist_insert refs s) d)
  | _, _ => true
end

end Smtm
