import WeakCore.TermPlantAtT
import WeakCore.TermOwnG0Defs
import WeakCore.TermW2New

/-! # TermPlantAtN: plumbing for `NoFulT`

The publish-of-`l` case of `NoFulT` (the step is `publish`: promises and `vWr` unchanged), and
the memory/run plumbing for the `winLe_gen` at `c'`.
-/

namespace TermPlantAtN
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A `publish` step keeps `vWr` and the promises. -/
theorem tstep_publish_vWr {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {y : String} {a : At}
    {e : Expr} {r : Memory × List Ts × TTh} (hterm : th.term = .let_ y (.publish a) e)
    (hr : r ∈ tstep g mem pairs th) :
    r.2.2.vs.vWr = th.vs.vWr ∧ r.2.2.promises = th.promises := by
  simp only [tstep, hterm, evalOp, List.mem_map] at hr
  obtain ⟨⟨s', t', ws⟩, hs, rfl⟩ := hr
  cases hev : evalAt th.env a with
  | none => simp [hev, ol] at hs
  | some q =>
    obtain ⟨t0, ws0⟩ := q
    simp only [hev, ol, bind, Option.bind, pure] at hs
    split at hs
    all_goals first
      | (simp at hs; done)
      | (cases hs with
         | head => exact ⟨rfl, rfl⟩
         | tail _ h => cases h)

/-- The publish case of `NoFulT`. -/
theorem noFul_pub {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {l : AllocLabel} {t : Ts} {mP : Msg} (hpub : TermOwnG0Defs.PubAt th l) (hr : r ∈ tstep g mem pairs th)
    (ht : t ∈ th.promises) (hle : th.vs.vWr ≤ mP.view) :
    t ∈ r.2.2.promises ∧ r.2.2.vs.vWr ≤ mP.view := by
  obtain ⟨y, a, e, -, -, -, hterm, -⟩ := hpub
  obtain ⟨h1, h2⟩ := tstep_publish_vWr hterm hr
  rw [h1, h2]
  exact ⟨ht, hle⟩

/-- The plant message persists along every solo run from `c'` (`hmB` of `winLe_gen`). -/
theorem mem_along {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {l : AllocLabel}
    {c c' : Cfg} {t : Ts} {mP : Msg} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th) (e1 : c'.mem = r.1) (hm : c.mem[t]? = some mP) :
    ∀ c2, TermOwnG0Defs.SoloNP p k arch i l c' c2 → c2.mem[t]? = some mP := by
  intro c2 hs
  obtain ⟨-, hme, -, -, -⟩ := TermCert.tstep_appUp hr
  have h1 : c'.mem[t]? = some mP := by rw [e1]; exact hme t mP hm
  exact W2New.solo_mem hs.toSolo h1

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The non-publish step keeps the plant edge outstanding (from K-3 `noFul_step`). -/
def NoFulStepT (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (p : Prog) (k : Promises.Knobs)
    (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel} {cl : Cell} {t : Ts},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → k.storeDepRts = true →
    Eg.sto l = some cl → cl.owner = some i → Eg.pfr l ≠ none → TermPlantAtT.KeyG Tot HP i l →
    tm Eg c i l = some t → ¬ TermOwnG0Defs.PubAt th l → t ∈ r.2.2.promises

/-- The window after the step (K-4 `noFulPlRun` from the typed start at `c'`, K-5
`winLe_gen`). -/
def WinAfterT (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (p : Prog) (k : Promises.Knobs)
    (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel} {cl : Cell} {t : Ts} {mP : Msg},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → k.storeDepRts = true →
    Eg.sto l = some cl → cl.owner = some i → Eg.pfr l ≠ none → TermPlantAtT.KeyG Tot HP i l →
    tm Eg c i l = some t → c.mem[t]? = some mP → ¬ TermOwnG0Defs.PubAt th l →
    t ∈ r.2.2.promises → r.2.2.vs.vWr ≤ mP.view

/-- **`NoFulT`** from the two K1-side facts, with the publish case done here. -/
theorem noFulT_of {tm : GEnv → Cfg → Nat → AllocLabel → Option Ts}
    (hS : NoFulStepT tm p k arch Sp Init MintOK c0) (hW : WinAfterT tm p k arch Sp Init MintOK c0) :
    TermPlantAtT.NoFulT tm p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r l cl t mP X hk hsto hown hpf hnp htm hmP htP hle
  by_cases hpub : TermOwnG0Defs.PubAt th l
  · exact noFul_pub hpub X.hr htP hle
  · have h1 := hS X hk hsto hown hpf hnp htm hpub
    exact ⟨h1, hW X hk hsto hown hpf hnp htm hmP hpub h1⟩

end

end TermPlantAtN

#print axioms TermPlantAtN.tstep_publish_vWr
#print axioms TermPlantAtN.noFul_pub
#print axioms TermPlantAtN.mem_along
#print axioms TermPlantAtN.noFulT_of
