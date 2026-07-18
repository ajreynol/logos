module

/-
Facade module: CongSupport was split into Cpc/Proofs/RuleSupport/Cong/*
(Core -> ValueRel -> HoCong -> ApplySpineA -> ApplySpineB -> TupleBvSeq ->
RegLanSpine -> Binders -> TypeSpine -> TrueSpine -> Impl), each importing the
previous. Importing this module provides the full CongSupport namespace.
-/
public import Cpc.Proofs.RuleSupport.Cong.Impl
import all Cpc.Proofs.RuleSupport.Cong.Impl

public section
