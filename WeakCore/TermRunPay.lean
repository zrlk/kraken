import WeakCore.TermPlantF
import WeakCore.TermIniPay

/-!
# TermRunPay: `RunAgree.pay` at a promise step, from the `SysInvN` box clauses

The promise-step half of the `RunAgree` field (`TermPlantF.RunAgreeF`) used to name the box-payload
part `pay` as a run fact.  It follows from `TermIni.runAgree_payW` and the `SysInvN` box clauses
(`boxPV`, `boxFrOwn`, `boxFrLe`, `payOwn`; `TermBoxZ`), the certificate's `FrBound` and the final
`MemInv`'s `BoxInv`.  `RunAgreeF2` is `RunAgreeF` without `pay`; `runAgreeF_of` gives `RunAgreeF`
back, so `RunAgreeF`'s consumers are unchanged.
-/

namespace TermRunPay
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped TermMain TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `TermIni.RunAgreeW` without its box-payload part `pay`. -/
structure RunAgreeW2 (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  ini : ∀ a, ((∃ c f, E0.sto a = some c ∧ E0.pfr a = some f) ∨ Lp a) → E2.ini a ≤ E'.ini a
  pfrB : ∀ a f, (∃ B, E0.box a = some B) → E2.pfr a = some f → ∃ f', E'.pfr a = some f' ∧ f' ≤ f

/-- (named run fact) `RunAgreeF` without `pay`: the counts and the frontiers at the start's boxes. -/
def RunAgreeF2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 →
      TermTyped.IniLoc (TermPlantF.IniZK Eg Tot HP j) (Cut Eg j S) E2 →
      TermTyped.IniHeld (TermTyped.WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      TermK5Defs.PfrProvE p k arch j (TermTyped.WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      TermK5O.PfrProvO p k arch j (TermTyped.WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      RunAgreeW2 (Cut Eg j S) (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w))
        (PlantL c Eg j th a v w) E2

/-- (named run fact) the `RunAgree` field, with the promise-step half `RunAgreeF2`. -/
def RunAgreeFT2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  RunAgreeF2 p k arch Sp Init MintOK c0 ∧ RunAgreeT p k arch Sp Init MintOK c0

/-- A planted label holds a cell of the promiser's cut. -/
theorem plantL_sto {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {S : AllocLabel → Prop} {l : AllocLabel} (h : PlantL c Eg j th a v w l) : ∃ cl, (Cut Eg j S).sto l = some cl := by
  obtain ⟨l', -, t, -, m, -, -, -, a', g, -, -, cl, hcl, -⟩ := h
  exact ⟨cl, hcl⟩

/-- **`RunAgreeF` from `RunAgreeF2`**: `pay` by `TermIni.runAgree_payW` from the box clauses. -/
theorem runAgreeF_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (h : RunAgreeF2 p k arch Sp Init MintOK c0) : RunAgreeF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO
  have h2 := h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO
  refine ⟨h2.ini, h2.pfrB, TermIni.runAgree_payW (n := c.mem.size) (v0 := th.vs.vWr) hfb hext.2.2.2.2.1
    hext.2.2.2.2.2.2.2.2.1 (fun l B hB => (hmi.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1) (fun l hl => plantL_sto hl)
    ?_ (fun l B hB => X.inv.boxPV l B hB) ?_ (fun l B hB => X.inv.boxFrLe l B hB)
    (fun l B hB w hw a' g hv cl hcl hpf => X.inv.payOwn l B hB w hw a' g hv cl (cutSto_sub hcl) hpf)⟩
  · intro a cl hcl hpf
    rcases (cutSto_some.1 hcl).2 with ho | ⟨f, hf⟩
    · exact ho
    · have e : Eg.pfr a = none := hpf
      rw [e] at hf; cases hf
  · intro l B hB ho
    exact X.inv.boxFrOwn l B hB th (by rw [ho]; exact X.hth)

end TermRunPay

#print axioms TermRunPay.plantL_sto
#print axioms TermRunPay.runAgreeF_of
