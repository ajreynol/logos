/-
Facade module: CongSupport was split into Cpc/Proofs/RuleSupport/Cong/*
(Core -> ValueRel -> HoCong -> ApplySpineA -> ApplySpineB -> TupleBvSeq ->
RegLanSpine -> Binders -> TypeSpine -> TrueSpine -> Impl), each importing the
previous. Importing this module provides the full CongSupport namespace.
-/
import Cpc.Proofs.RuleSupport.Cong.Impl
