import WeakCore.TermRunPay
import WeakCore.TermVwrLt
import WeakCore.TermBoxPV

/-!
# TermRunPayT: `RunAgree.pay` at a thread step, from the `SysInvN` box clauses

The thread-step half of the `RunAgree` field (`TermPlantF.RunAgreeT`) named the box-payload part
`pay` as a run fact.  It follows from `TermIni.runAgree_payW` at the stepper's post-step environment
`E'`, which is its cut of the post-step global environment (`TermInterf.tctx_cut`): the box clauses
of `EgT` are the thread-step preservation lemmas (`TermBoxPV.boxPV_thread` with the step's
`BoxNewV`, now exported by `TOut`; `TermBoxOwn.boxFrOwnT_of`, `TermVwrLt.boxFrLtT_of`,
`TermBoxOwn.payOwnT_of`).  `RunAgreeT2` is `RunAgreeT` without `pay`; `runAgreeT_of` gives
`RunAgreeT` back (given the run's initial `ViewInv`), so `RunAgreeT`'s consumers are unchanged.
-/

namespace TermRunPayT
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped TermMain TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (named run fact) `RunAgreeT` without `pay`: the counts and the frontiers at the start's boxes. -/
def RunAgreeT2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ c1 th1 E1, Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 → Ext E' E1 →
      MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) → FrBound E' c'.mem.size r.2.2.vs.vWr E1 →
      TermTyped.IniLoc (IniZTK Eg Tot HP i th) E' E1 →
      TermTyped.IniHeld (TermTyped.WitP c'.mem r.2.2.promises) E' E1 th1.vs.vWr →
      TermK5O.PfrProvO p k arch i (TermTyped.WitP c'.mem r.2.2.promises) E' c' c1 E1 →
      TermRunPay.RunAgreeW2 E' E' (fun _ => False) E1

/-- (named run fact) the `RunAgree` field, both halves without `pay`. -/
def RunAgreeFT3 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  TermRunPay.RunAgreeF2 p k arch Sp Init MintOK c0 ∧ RunAgreeT2 p k arch Sp Init MintOK c0

/-- **`RunAgreeT` from `RunAgreeT2`**: `pay` by `TermIni.runAgree_payW` at `E' = Cut EgT i E'.seen`,
from the post-step box clauses. -/
theorem runAgreeT_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hvi : TermViewInv.ViewInvR p k arch Sp c0) (h : RunAgreeT2 p k arch Sp Init MintOK c0) : RunAgreeT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPfrP c1 th1 E1 hs hc hth1
    hext hmi hfb hIL hIH hPO
  have h2 := h X Y Z hPfrP c1 th1 E1 hs hc hth1 hext hmi hfb hIL hIH hPO
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hcut := TermInterf.tctx_cut X Y ZC
  have hcb : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box = E'.box := congrArg TEnv.box hcut
  have hcs : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i = E'.sto := congrArg TEnv.sto hcut
  have hcp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr = E'.pfr := by
    have e := congrArg TEnv.pfr hcut
    exact e
  have hct : i = E'.tid := congrArg TEnv.tid hcut
  have hbox' : ∀ l B, E'.box l = some B →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B := fun l B hB => by
    rw [hcb]; exact hB
  have hL1 : ∀ l B, E'.box l = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat), w.val = .loc a' g →
      w.view < B.fr := fun l B hB =>
    TermBoxPV.boxPV_thread X Y ZC Z.2.2.2.2.2.2.2.2.1 (TermViewInv.viewInv_run hvi X.run) X.inv.boxPV l B
      (hbox' l B hB)
  have hLn : ∀ l B, E'.box l = some B → B.fr ≤ c'.mem.size - 1 := fun l B hB =>
    TermVwrLt.boxFrLtT_of X Y ZC X.inv.vwrLt X.inv.boxFrLt l B (hbox' l B hB)
  have hdisj : ∀ l B, E1.box l = some B → E1.sto l = none := fun l B hB =>
    (hmi.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
  have hsto : ∀ l c, E'.sto l = some c → E1.sto l = some c := hext.2.2.2.2.1
  have hbx : ∀ l B, E'.box l = some B → E1.box l = some B := hext.2.2.2.2.2.2.2.2.1
  refine TermIni.RunAgree_ofW ⟨h2.ini, h2.pfrB, ?_⟩ (fun a f hL _ => hL.elim)
  by_cases hs0 : c'.mem.size = 0
  · -- empty memory: every box frontier is `0`, so no payload reference
    intro a B hG hB w hw a' g hv _
    have hB0 : E'.box a = some B := by
      have hsn : ∀ c, E'.sto a = some c → False := fun c hc => by
        have e := hsto a c hc; rw [hdisj a B hB] at e; cases e
      rcases hG with ⟨c, f, hc, -⟩ | hLa | ⟨B0, hB0⟩
      · exact (hsn c hc).elim
      · exact hLa.elim
      · rw [hbx a B0 hB0] at hB; cases hB; exact hB0
    have h1 := hL1 a B hB0 w hw a' g hv
    have h3 := hLn a B hB0
    rw [hs0] at h3
    exact absurd (Nat.lt_of_lt_of_le h1 h3) (Nat.not_lt_zero _)
  · obtain ⟨n, hn⟩ : ∃ n, c'.mem.size = n + 1 := ⟨c'.mem.size - 1, by omega⟩
    have hfb' : FrBound E' (n + 1) r.2.2.vs.vWr E1 := by rw [← hn]; exact hfb
    refine TermIni.runAgree_payW (n := n) hfb' hsto hbx hdisj (fun l hl => hl.elim) ?_ hL1 ?_
      (fun l B hB => by have h3 := hLn l B hB; rw [hn] at h3; exact h3) ?_
    · intro a cl hcl hpf
      have hcl' : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i a = some cl := by
        rw [hcs]; exact hcl
      rw [← hct]
      rcases (cutSto_some.1 hcl').2 with ho | ⟨f, hf⟩
      · exact ho
      · rw [hcp, hpf] at hf; cases hf
    · intro l B hB ho
      exact TermBoxOwn.boxFrOwnT_of X Y ZC X.inv.boxFrOwn l B (hbox' l B hB) r.2.2
        (by rw [ho, ← hct]; exact X.e3)
    · intro l B hB w hw a' g hv cl hcl hpf
      have hcl' : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i a'.label = some cl := by
        rw [hcs]; exact hcl
      exact TermBoxOwn.payOwnT_of X Y ZC X.inv.boxSto X.inv.payOwn l B (hbox' l B hB) w hw a' g hv cl
        (cutSto_sub hcl') (by rw [hcp]; exact hpf)

/-- **`RunAgreeFT2` from `RunAgreeFT3`** (the `ObligationsF` field's old shape). -/
theorem runAgreeFT2_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hvi : TermViewInv.ViewInvR p k arch Sp c0) (h : RunAgreeFT3 p k arch Sp Init MintOK c0) :
    TermRunPay.RunAgreeFT2 p k arch Sp Init MintOK c0 :=
  ⟨h.1, runAgreeT_of hvi h.2⟩

end TermRunPayT

#print axioms TermRunPayT.runAgreeT_of
#print axioms TermRunPayT.runAgreeFT2_of
