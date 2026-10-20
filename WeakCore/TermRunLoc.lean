import WeakCore.TermRunPayT
import WeakCore.TermGbLp
import WeakCore.TermOwnG0
import WeakCore.TermOwnG0P
import WeakCore.TermCertScope
import WeakCore.TermK5Lp

/-!
# TermRunLoc: `RunAgree` locality from the run's `FrBound`

`FrBound` (TermTyped) now also records the run's locality (from the step footprint `EFoot`/`Foot`):
the thread is fixed, the start's cells stay, and at a start cell not owned by the thread the count
and the frontier are unchanged; a start box (no cell) stays, with no cell and the frontier unchanged.
So `RunAgreeW2.pfrB` holds outright (`pfrB_of`), and `RunAgreeW2.ini` holds except at the thread's
own start cells (`ini_of`).  `RunAgreeW3` keeps only that residual (`iniOwn`): the run's count at an
own start cell that is published (has a frontier) or planted (`Lp`) is at most the step's.
`RunAgreeF3`/`RunAgreeT3` are `RunAgreeF2`/`RunAgreeT2` with `RunAgreeW3`; `runAgreeF2_of`,
`runAgreeT2_of` give the old forms back, so their consumers are unchanged.
(iniop) At the start's published cells (`IniZF`; at a thread step also the cell it publishes, `IniZT`)
the run keeps the counts (`IniLoc`, a premise of every form), so the residual `RunAgreeW3Z` is only at
the other own cells, or planted ones without a start frontier (`runAgreeW3_of_iniLoc`).
(G-b) At a planted cell the residual is only after the root's publish (`root`); before it the run's
held counts (`IniHeld`, a premise of `RunAgreeF3`) and the G-0 contract bound it (`TermGbLp.iniLp_of`),
with the non-buffer count fact `CapN` (`runAgreeW3Z_of_G`).  (gb2) Both are discharged here: the G-0
window by `TermOwnG0.g0WinT_ofP` at the promiser's own start witness (`rootH0P`), `CapNAt` by
`TermGbLp.capNAt_of`.
 After the root's publish the run's added units carry witnesses at most the publishing thread's
`vWr` (`TermK5Defs.PfrProvE`, a premise of `RunAgreeF3`), which the G-0 window at the publishing
configuration bounds (`TermK5Lp.iniLp_ofV`): `root` is discharged and the residual is `RunAgreeW3K`
(`runAgreeW3Z_of_K`).  `RunAgreeF3Gb2` is the gb2 form (`runAgreeF3_of_gb2`).
-/

namespace TermRunLoc
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped TermMain TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The residual of `RunAgreeW2`: the counts at the thread's own published or planted start cells. -/
structure RunAgreeW3 (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  iniOwn : ∀ a c, E0.sto a = some c → c.owner = some E0.tid → ((∃ f, E0.pfr a = some f) ∨ Lp a) →
    E2.ini a ≤ E'.ini a

/-- **`RunAgreeW2` from the residual and `FrBound`'s locality**, at a step environment `E'` that
agrees with `E0` off `Lp` and only raises counts, `Lp` labels being own start cells. -/
theorem runAgreeW2_of {E0 E' E2 : TEnv} {Lp : AllocLabel → Prop} {n0 v0 : Nat}
    (hfb : FrBound E0 n0 v0 E2) (hx : Ext E0 E2) (hdis : ∀ l B, E2.box l = some B → E2.sto l = none)
    (hini : ∀ a, E0.ini a ≤ E'.ini a) (hpf : ∀ a, ¬ Lp a → E'.pfr a = E0.pfr a)
    (hL : ∀ a, Lp a → ∃ c, E0.sto a = some c ∧ c.owner = some E0.tid)
    (h : RunAgreeW3 E0 E' Lp E2) : TermRunPay.RunAgreeW2 E0 E' Lp E2 := by
  refine ⟨fun a ha => ?_, fun a f ⟨B, hB⟩ hf => ?_⟩
  · have hc : ∃ c, E0.sto a = some c := by
      rcases ha with ⟨c, -, hc, -⟩ | hl
      · exact ⟨c, hc⟩
      · obtain ⟨c, hc, -⟩ := hL a hl; exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := hc
    by_cases ho : c.owner = some E0.tid
    · refine h.iniOwn a c hc ho ?_
      rcases ha with ⟨c1, f, -, hf⟩ | hl
      · exact .inl ⟨f, hf⟩
      · exact .inr hl
    · rw [((hfb.2.2.2.1.2 a c hc).2 ho).1]; exact hini a
  · have hB2 : E2.box a = some B := hx.2.2.2.2.2.2.2.2.1 a B hB
    have hs0 : E0.sto a = none := by
      cases e : E0.sto a with
      | none => rfl
      | some c => have e2 := hx.2.2.2.2.1 a c e; rw [hdis a B hB2] at e2; cases e2
    have hnl : ¬ Lp a := fun hl => by obtain ⟨c, hc, -⟩ := hL a hl; rw [hs0] at hc; cases hc
    refine ⟨f, ?_, Nat.le_refl _⟩
    rw [hpf a hnl, ← (hfb.2.2.2.2 a B hB hs0).2.2]; exact hf

/-- (iniop) The residual of `RunAgreeW3` outside the run's locality labels `Z`: at the thread's own
start cells not in `Z`, or planted ones without a start frontier. -/
structure RunAgreeW3Z (Z : AllocLabel → Prop) (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  iniOwn : ∀ a c, E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    ((∃ f, E0.pfr a = some f) ∨ Lp a) → E2.ini a ≤ E'.ini a

/-- (iniop) **`RunAgreeW3` from its residual outside `Z` and the run's `IniLoc`** at a step
environment that only raises counts. -/
theorem runAgreeW3_of_iniLoc {Z Lp : AllocLabel → Prop} {E0 E' E2 : TEnv}
    (hini : ∀ a, E0.ini a ≤ E'.ini a) (hI : IniLoc Z E0 E2) (h : RunAgreeW3Z Z E0 E' Lp E2) :
    RunAgreeW3 E0 E' Lp E2 := by
  refine ⟨fun a c hc ho hp => ?_⟩
  cases e : E0.pfr a with
  | none => exact h.iniOwn a c hc ho (.inr e) hp
  | some f =>
    by_cases hz : Z a
    · rw [(hI a c f hz hc e).1]; exact hini a
    · exact h.iniOwn a c hc ho (.inl hz) hp

/-- (G-b) The promise-step residual: (`iniOwnN`, F/¬Lp) the own published start cells outside `Z` that
are not planted; (`root`) at each planted own start cell `a` outside `Z` or without a start frontier,
either the old count bound, or the cell's count after a `publish` naming `a` (before it, the G-0
window and `CapNAt` bound it, `runAgreeW3Z_of_G`).  The old residual `RunAgreeW3Z` implies it
(`runAgreeF3_of_old`). -/
structure RunAgreeW3G (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (Z : AllocLabel → Prop) (E0 E' : TEnv)
    (Lp : AllocLabel → Prop) (E2 : TEnv) (c2 : Cfg) : Prop where
  iniOwnN : ∀ a c, E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    (∃ f, E0.pfr a = some f) → ¬ Lp a → E2.ini a ≤ E'.ini a
  root : ∀ a c, Lp a → E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    E2.ini a ≤ E'.ini a ∨
      (¬ TermOwnG0Defs.SoloNP p k arch i a (promise cP i a0 v0 w) c2 → E2.ini a ≤ E'.ini a)

/-- The promise-step residual: only the own published start cells that are not planted. -/
structure RunAgreeW3K (Z : AllocLabel → Prop) (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  iniOwnN : ∀ a c, E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    (∃ f, E0.pfr a = some f) → ¬ Lp a → E2.ini a ≤ E'.ini a

/-- (G-b) **The last plant edge of a planted label** `l`: an outstanding promise `t` of the promiser
(the new one, or an older one) whose message `⟨b, .loc a' g, wt⟩` at a `noOwn`, region-free cell
names `l`, with `wt` below the memory size before the promise. -/
theorem plantRoot {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} (hth : c.ths[j]? = some th) (hw : w < c.mem.size)
    (hvl : ∀ t, t ∈ th.promises → ∃ m : Msg, c.mem[t]? = some m ∧ m.view < t)
    (hl : PlantL c Eg j th a v w l) :
    ∃ t b a' g wt ca cr, (t = c.mem.size ∨ t ∈ th.promises) ∧
      (promise c j a v w).mem[t]? = some ⟨b, .loc a' g, wt⟩ ∧ a'.label = l ∧
      (cutP Eg j).sto b.label = some ca ∧ Ty.noOwnIn [] ca.ty = true ∧ rgnFree ca.ty = true ∧
      (cutP Eg j).sto l = some cr ∧ wt < c.mem.size := by
  obtain ⟨l', -, t, ht, m, hm, hml, ⟨ca, hca, hno, hrf⟩, a', g, hv, hal, cr, hcr, -, -⟩ := hl
  have hpm : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp only [promise, hth]
  obtain ⟨b, mv, wt⟩ := m
  simp only at hv hml
  subst hv
  refine ⟨t, b, a', g, wt, ca, cr, ?_, by rw [hpm]; exact hm, hal, by rw [hml]; exact hca, hno, hrf,
    hcr, ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_singleton.1 h)
  · rcases List.mem_append.1 ht with h | h
    · obtain ⟨m', hm', hvw⟩ := hvl t h
      have hlt : t < c.mem.size := by
        rcases Nat.lt_or_ge t c.mem.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at hm'; cases hm'
      rw [Array.getElem?_push_lt hlt] at hm
      rw [Array.getElem?_eq_getElem hlt, hm] at hm'
      cases hm'
      exact Nat.lt_trans hvw hlt
    · rw [List.mem_singleton.1 h, Array.getElem?_push_size] at hm
      cases hm
      exact hw

/-- (G-b) **`RunAgreeW3Z` from the residual `RunAgreeW3G`** and the run's held counts, at the plant's
environment `E' = plantE E0 …`. -/
theorem runAgreeW3Z_of_G {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP c2 : Cfg} {i : Nat} {thP th2 : TTh}
    {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {Z Lp : AllocLabel → Prop} {E0 E2 : TEnv}
    (hrl : ∀ l, E0.rini l ≤ E0.ini l) (hc2 : Certified p k arch c2 i)
    (hth2 : c2.ths[i]? = some th2) (hIH : IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr)
    {g : G} {s2 : St} (hext : Ext E0 E2) (hmi : MemInv g E2 s2)
    (h : RunAgreeW3G p k arch cP i a0 v0 w Z E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2 c2)
    (hG : ∀ a, Lp a → ∃ wt, wt < cP.mem.size ∧ TermOwnG0W.G0WinW p k arch cP i a0 v0 w a wt) :
    RunAgreeW3Z Z E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2 := by
  refine ⟨fun a c hc ho hz hp => ?_⟩
  by_cases hL : Lp a
  · rcases h.root a c hL hc ho hz with hb | hpp
    · exact hb
    obtain ⟨wt, hwt, hG⟩ := hG a hL
    by_cases hNP : TermOwnG0Defs.SoloNP p k arch i a (promise cP i a0 v0 w) c2
    · exact TermGbLp.iniLp_of hwt hrl hG hNP hc2 hth2 hIH hext hmi hL hc ho (TermGbLp.capNAt_of hrl hIH a)
    · exact hpp hNP
  · exact h.iniOwnN a c hc ho hz (hp.resolve_right hL) hL

/-- **`RunAgreeW3Z` from `RunAgreeW3K`**: at a planted label, before the root's publish by the
G-0 window (`iniLp_of`); after it by the provenance `PfrProvE` and the window at the publishing
configuration `c1` (certified: `certified_back`), `iniLp_ofV`. -/
theorem runAgreeW3Z_of_K {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP c2 : Cfg} {i : Nat} {thP th2 : TTh}
    {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {Z Lp : AllocLabel → Prop} {E0 E2 : TEnv}
    (hrl : ∀ l, E0.rini l ≤ E0.ini l) (hc2 : Certified p k arch c2 i)
    (hth2 : c2.ths[i]? = some th2) (hIH : IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr)
    {g : G} {s2 : St} (hext : Ext E0 E2) (hmi : MemInv g E2 s2)
    (hpv : TermK5Defs.PfrProvE p k arch i (WitP cP.mem thP.promises) E0 (promise cP i a0 v0 w) c2 E2)
    (hLpf : ∀ a, Lp a → E0.pfr a = none)
    (h : RunAgreeW3K Z E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2)
    (hG : ∀ a, Lp a → ∃ wt, wt < cP.mem.size ∧ TermOwnG0W.G0WinW p k arch cP i a0 v0 w a wt) :
    RunAgreeW3Z Z E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2 := by
  refine ⟨fun a c hc ho hz hp => ?_⟩
  by_cases hL : Lp a
  · obtain ⟨wt, hwt, hG⟩ := hG a hL
    have hcap := TermGbLp.capNAt_of hrl hIH a
    rcases hpv a c hc ho (hLpf a hL) with ⟨-, hNP⟩ | ⟨F, c1, th1, c1', -, hNP, hth1, -, hs, hsolo, hu⟩
    · exact TermGbLp.iniLp_of hwt hrl hG hNP hc2 hth2 hIH hext hmi hL hc ho hcap
    · have hc1 : Certified p k arch c1 i := TermGlob.certified_back (.thread hs hsolo) hc2
      have hv : th1.vs.vWr ≤ wt := hG c1 th1 hNP hc1 hth1
      exact TermK5Lp.iniLp_ofV (Nat.lt_of_le_of_lt hv hwt) hrl hIH hext hmi hL hc ho hcap hu
  · exact h.iniOwnN a c hc ho hz (hp.resolve_right hL) hL

/-- (named run fact) `RunAgreeF2` with only the own-cell count residual. -/
def RunAgreeF3 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → IniLoc (IniZF Eg) (Cut Eg j S) E2 →
      IniHeld (WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      TermK5Defs.PfrProvE p k arch j (WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      RunAgreeW3K (IniZF Eg) (Cut Eg j S)
        (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) (PlantL c Eg j th a v w) E2

/-- (named run fact) `RunAgreeT2` with only the own-cell count residual. -/
def RunAgreeT3 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ c1 th1 E1, Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 → Ext E' E1 →
      MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) → FrBound E' c'.mem.size r.2.2.vs.vWr E1 →
      IniLoc (IniZT Eg i th) E' E1 → RunAgreeW3Z (IniZT Eg i th) E' E' (fun _ => False) E1

/-- (named run fact) the `RunAgree` field: both halves, only the own-cell count residual. -/
def RunAgreeFT4 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  RunAgreeF3 p k arch Sp Init MintOK c0 ∧ RunAgreeT3 p k arch Sp Init MintOK c0

/-- (runAgree) `IniLoc` is antitone in the locality set. -/
theorem iniLoc_mono {Z Z2 : AllocLabel → Prop} {E0 E : TEnv} (hZ : ∀ a, Z2 a → Z a) (h : IniLoc Z E0 E) :
    IniLoc Z2 E0 E :=
  fun a c f hz hc hf => h a c f (hZ a hz) hc hf

/-- (named run fact; runAgree) `RunAgreeF3` at the locality set `IniZK` (the published cells and
the promiser's key-less own cells), with the post-publish provenance `PfrProvO`. -/
def RunAgreeF3K (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → IniLoc (IniZK Eg Tot HP j) (Cut Eg j S) E2 →
      IniHeld (WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      TermK5Defs.PfrProvE p k arch j (WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      TermK5O.PfrProvO p k arch j (WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2 →
      RunAgreeW3K (IniZF Eg) (Cut Eg j S)
        (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) (PlantL c Eg j th a v w) E2

/-- (named run fact; runAgree) `RunAgreeT3` at the locality set `IniZTK`, with the run's held
counts `IniHeld` and the post-publish provenance `PfrProvO`. -/
def RunAgreeT3K (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ c1 th1 E1, Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 → Ext E' E1 →
      MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) → FrBound E' c'.mem.size r.2.2.vs.vWr E1 →
      IniLoc (IniZTK Eg Tot HP i th) E' E1 → IniHeld (WitP c'.mem r.2.2.promises) E' E1 th1.vs.vWr →
      TermK5O.PfrProvO p k arch i (WitP c'.mem r.2.2.promises) E' c' c1 E1 →
      RunAgreeW3Z (IniZT Eg i th) E' E' (fun _ => False) E1

/-- (runAgree) `RunAgreeF3K` is weaker than `RunAgreeF3` (`IniZF ⊆ IniZK`). -/
theorem runAgreeF3K_of_F3 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h : RunAgreeF3 p k arch Sp Init MintOK c0) : RunAgreeF3K p k arch Sp Init MintOK c0 :=
  fun X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV _ =>
    h X S c2 th2 E2 hs hc hth2 hext hmi hfb (iniLoc_mono (fun _ hz => .inl hz) hIL) hIH hPV

/-- (runAgree) `RunAgreeT3K` is weaker than `RunAgreeT3` (`IniZT ⊆ IniZTK`). -/
theorem runAgreeT3K_of_T3 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h : RunAgreeT3 p k arch Sp Init MintOK c0) : RunAgreeT3K p k arch Sp Init MintOK c0 :=
  fun X Y Z hPfrP c1 th1 E1 hs hc hth1 hext hmi hfb hIL _ _ =>
    h X Y Z hPfrP c1 th1 E1 hs hc hth1 hext hmi hfb (iniLoc_mono (fun _ hz => .inl hz) hIL)

/-- (the weakening check) `RunAgreeF3` as it stood at gb2. -/
def RunAgreeF3Gb2 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → IniLoc (IniZF Eg) (Cut Eg j S) E2 →
      IniHeld (WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      RunAgreeW3G p k arch c j a v w (IniZF Eg) (Cut Eg j S)
        (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) (PlantL c Eg j th a v w) E2 c2

/-- **The new `RunAgreeF3` is weaker than gb2's**: an extra premise (`PfrProvE`), and only
`iniOwnN` of the residual. -/
theorem runAgreeF3_of_gb2 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h : RunAgreeF3Gb2 p k arch Sp Init MintOK c0) : RunAgreeF3 p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH _
  exact ⟨(h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH).iniOwnN⟩

/-- **The `runAgree` field is weaker than at gb2**. -/
theorem runAgreeFT4_gb2_imp_new {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg}
    (h : RunAgreeF3Gb2 p k arch Sp Init MintOK c0 ∧ RunAgreeT3 p k arch Sp Init MintOK c0) :
    RunAgreeFT4 p k arch Sp Init MintOK c0 :=
  ⟨runAgreeF3_of_gb2 h.1, h.2⟩

/-- (G-b, the weakening check) `RunAgreeF3` as it stood before G-b: the residual `RunAgreeW3Z`, without
the `IniHeld` premise. -/
def RunAgreeF3Old (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → IniLoc (IniZF Eg) (Cut Eg j S) E2 →
      RunAgreeW3Z (IniZF Eg) (Cut Eg j S) (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w))
        (PlantL c Eg j th a v w) E2

/-- (G-b) **The new `RunAgreeF3` is weaker than the old**: drop the `IniHeld` premise, take the old
bound in `root`'s left disjunct. -/
theorem runAgreeF3_of_old {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h : RunAgreeF3Old p k arch Sp Init MintOK c0) : RunAgreeF3 p k arch Sp Init MintOK c0 := by
  refine runAgreeF3_of_gb2 ?_
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL _
  have h3 := h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL
  exact ⟨fun l cl hcl ho hz hp _ => h3.iniOwn l cl hcl ho hz (Or.inl hp),
    fun l cl hL hcl ho hz => Or.inl (h3.iniOwn l cl hcl ho hz (Or.inr hL))⟩

/-- (G-b) **The `runAgree` field is weaker than before G-b**: `RunAgreeFT4` from the old `RunAgreeF3`
and the (unchanged) `RunAgreeT3`. -/
theorem runAgreeFT4_old_imp_new {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg}
    (h : RunAgreeF3Old p k arch Sp Init MintOK c0 ∧ RunAgreeT3 p k arch Sp Init MintOK c0) :
    RunAgreeFT4 p k arch Sp Init MintOK c0 :=
  ⟨runAgreeF3_of_old h.1, h.2⟩

/-- (gb2) **The G-0 start witness** at a planted label `r` with `(cutP Eg j).pfr r = none` (the last
plant edge's): the promiser's own cut `Cut Eg j S0` after the promise, unchanged (`Ext_refl`,
`FrBound_refl`; `RiniHeld` from `rini ≤ ini`). -/
theorem rootH0P {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {S0 : AllocLabel → Prop} (hS0 : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S0)
    {r : AllocLabel} {cl : Cell} (hpf : (cutP Eg j).pfr r = none) :
    ∃ E0 : TEnv, E0 = Cut Eg j S0 ∧ (∀ l, E0.sto l = (cutP Eg j).sto l) ∧ ∃ th1 E,
      (promise c j a v w).ths[j]? = some th1 ∧
      TermOwnG0.InvAtXRB p k arch j E0 (promise c j a v w).mem.size th.vs.vWr c.mem th.promises r cl
        (promise c j a v w) th1 E ∧ E.pfr r = none := by
  obtain ⟨-, hTE, hm, -⟩ := id hS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hTE2 := hTE
  obtain ⟨ρ, η, cx, hη, -⟩ := hTE2
  have hmP : MemInv (gOf p k arch (promise c j a v w) j) (Cut Eg j S0) (stOf (promise c j a v w).mem
      (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) := by
    rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm
  refine ⟨Cut Eg j S0, rfl, fun _ => rfl, { th with promises := th.promises ++ [c.mem.size] }, Cut Eg j S0, hpi.2.1,
    ⟨?_, hTE, hmP, hSC, ?_, FrBound_refl _ _ _, ⟨⟨Nat.le_refl _, Nat.le_refl _,
      fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e)⟩, TermTyped.anchR_start hmP
        (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh j th S0 X.hth))
        (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
          (by show c.mem.size - 1 ≤ (promise c j a v w).mem.size - 1; rw [hpi.1, Array.size_push]; exact Nat.sub_le_sub_right (Nat.le_succ _) 1)), .inl rfl⟩,
      fun _ _ _ _ _ o h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (X.inv.rle r))) h2⟩, hpf⟩
  · have hx := Ext_refl (Coh_CE η) (CohR_CE η); rw [hη] at hx; exact hx
  · rw [gOf_promise]; exact X.inv.bf

/-- (gb2, the weakening check) The G-b root premise, kept for `runAgreeF3_of_gb`. -/
def RootPfrGb (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address) (v0 : WeakMem.Val)
    (w : Ts) (Ec : TEnv) (P0 : List Ts) (r : AllocLabel) : Prop :=
  ∃ E0 n0 vw cl, (∀ l c, Ec.sto l = some c → E0.sto l = some c) ∧ E0.sto r = some cl ∧
    InvAtXR p k arch i E0 n0 vw cP.mem P0 r cl (promise cP i a0 v0 w) ∧
    TermOwnG0.PfrX p k arch cP i a0 v0 w r E0 n0 vw cP.mem P0 r cl

/-- (gb2, the weakening check) The G-b promise-step residual. -/
structure RunAgreeW3GGb (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (Ec : TEnv) (P0 : List Ts) (Z : AllocLabel → Prop) (E0 E' : TEnv)
    (Lp : AllocLabel → Prop) (E2 : TEnv) (c2 : Cfg) : Prop where
  iniOwnN : ∀ a c, E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    (∃ f, E0.pfr a = some f) → ¬ Lp a → E2.ini a ≤ E'.ini a
  root : ∀ a c, Lp a → E0.sto a = some c → c.owner = some E0.tid → (¬ Z a ∨ E0.pfr a = none) →
    E2.ini a ≤ E'.ini a ∨ (RootPfrGb p k arch cP i a0 v0 w Ec P0 a ∧ TermGbLp.CapNAt E0 E2 a ∧
      (¬ TermOwnG0Defs.SoloNP p k arch i a (promise cP i a0 v0 w) c2 → E2.ini a ≤ E'.ini a))

/-- (gb2, the weakening check) `RunAgreeF3` as it stood at G-b. -/
def RunAgreeF3Gb (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (S : AllocLabel → Prop) c2 th2 E2, Solo p k arch j (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → Ext (Cut Eg j S) E2 → MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2) →
      FrBound (Cut Eg j S) (c.mem.size + 1) th.vs.vWr E2 → IniLoc (IniZF Eg) (Cut Eg j S) E2 →
      IniHeld (WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr →
      RunAgreeW3GGb p k arch c j a v w (cutP Eg j) th.promises (IniZF Eg) (Cut Eg j S)
        (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) (PlantL c Eg j th a v w) E2 c2

/-- (gb2) **The new `RunAgreeF3` is weaker than G-b's**: drop `RootPfr` and `CapNAt` from `root`. -/
theorem runAgreeF3_of_gb {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h : RunAgreeF3Gb p k arch Sp Init MintOK c0) : RunAgreeF3 p k arch Sp Init MintOK c0 := by
  refine runAgreeF3_of_gb2 ?_
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH
  have h3 := h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH
  exact ⟨h3.iniOwnN, fun l cl hL hcl ho hz => (h3.root l cl hL hcl ho hz).imp id (fun h => h.2.2)⟩

/-- (gb2) **The `runAgree` field is weaker than at G-b**. -/
theorem runAgreeFT4_gb_imp_new {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg}
    (h : RunAgreeF3Gb p k arch Sp Init MintOK c0 ∧ RunAgreeT3 p k arch Sp Init MintOK c0) :
    RunAgreeFT4 p k arch Sp Init MintOK c0 :=
  ⟨runAgreeF3_of_gb h.1, h.2⟩

/-- **`RunAgreeF2` from `RunAgreeF3`**: planted labels are own start cells (`plantOf`'s `PlantR`
edge), `plantE` changes only the planted labels and raises counts; (G-b) the G-0 window at a planted
label is (gb2) `TermOwnG0.g0WinT_ofP` at its last plant edge (`plantRoot`) and the promiser's start
witness (`rootH0P`), with the certificate's scope and `NoHoldPub` from the raw run facts `hS`/`hWn`. -/
theorem runAgreeF2_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (_hk : k.storeDepRts = true) (hP : ProgT p) [ProgRetIall p] [TermTyped.WrIniC]
    (hS : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hWn : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
    (h : RunAgreeF3K p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermRunPay.RunAgreeF2 p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO
  have hvl : ∀ t, t ∈ th.promises → ∃ m : Msg, c.mem[t]? = some m ∧ m.view < t :=
    fun t ht => promViewLt_run h0 X.run j th t X.hth ht
  have hpl : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => by
    obtain ⟨m, hm, -⟩ := hvl t ht
    rcases Nat.lt_or_ge t c.mem.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hm; cases hm
  have hG : ∀ l, PlantL c Eg j th a v w l →
      ∃ wt, wt < c.mem.size ∧ TermOwnG0W.G0WinW p k arch c j a v w l wt := by
    intro l hl
    have hpf : (cutP Eg j).pfr l = none := by
      obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, -, -, hpf⟩ := hl
      subst hal; exact hpf
    obtain ⟨t, b, a', g, wt, ca, cr0, -, hmt, ha, hca, hno, hrf, hcr, hwt⟩ := plantRoot X.hth X.hw hvl hl
    obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
    obtain ⟨E0, hE0e, hE0, h0P⟩ := rootH0P (cl := cr0) X hS0 hpf
    have hcr0 : E0.sto l = some cr0 := by rw [hE0]; exact hcr
    exact ⟨wt, hwt, TermOwnG0.g0WinT_ofP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (hS X) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw)
      (fun c1 h1 h2 => by rw [hE0e]; exact (hWn X).1 S0 hS0 c1 h1 h2) X.hth hpl hcr0
      (TermCert.winInv_prom (TermCert.winInv_refl X.hth)) h0P hmt ha (by rw [hE0]; exact hca) hno hrf hcr0⟩
  have hini : ∀ l, (Cut Eg j S).ini l ≤ (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)).ini l :=
    fun l => by
      by_cases hl : PlantL c Eg j th a v w l
      · rw [plantE_ini_in hl]; exact Nat.le_max_left _ _
      · rw [plantE_ini_ne hl]; exact Nat.le_refl _
  refine runAgreeW2_of hfb hext (fun l B hB => (hmi.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1) hini
    (fun l hl => plantE_pfr_ne hl) (fun l hl => ?_)
    (runAgreeW3_of_iniLoc hini (iniLoc_mono (fun _ hz => .inl hz) hIL) (runAgreeW3Z_of_K (fun l => X.inv.rle l) hc hth2 hIH hext hmi hPV
      (fun l hl => by
        obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, -, -, hpf⟩ := hl
        subst hal; exact hpf)
      (h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO) hG))
  · obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, -⟩ := hl
    subst hal
    exact ⟨cl1, hc1, ho1⟩

/-- **`RunAgreeT2` from `RunAgreeT3`**: no planted labels, `E0 = E'`. -/
theorem runAgreeT2_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (h : RunAgreeT3K p k arch Sp Init MintOK c0) : TermRunPayT.RunAgreeT2 p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPfrP c1 th1 E1 hs hc hth1
    hext hmi hfb hIL hIH hPO
  exact runAgreeW2_of hfb hext (fun l B hB => (hmi.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1) (fun _ => Nat.le_refl _)
    (fun _ _ => rfl) (fun _ hl => hl.elim)
    (runAgreeW3_of_iniLoc (fun _ => Nat.le_refl _) (iniLoc_mono (fun _ hz => .inl hz) hIL)
      (h X Y Z hPfrP c1 th1 E1 hs hc hth1 hext hmi hfb hIL hIH hPO))

/-- The `RunAgree` field from `RunAgreeFT4`. -/
theorem runAgreeFT3_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hk : k.storeDepRts = true) (hP : ProgT p) [ProgRetIall p] [TermTyped.WrIniC]
    (hS : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hWn : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
    (h : RunAgreeFT4 p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermRunPayT.RunAgreeFT3 p k arch Sp Init MintOK c0 :=
  ⟨runAgreeF2_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) h0 hk hP hS hWn (runAgreeF3K_of_F3 h.1),
    runAgreeT2_of (runAgreeT3K_of_T3 h.2)⟩

end TermRunLoc

#print axioms TermRunLoc.runAgreeW2_of
#print axioms TermRunLoc.runAgreeW3_of_iniLoc
#print axioms TermRunLoc.plantRoot
#print axioms TermRunLoc.rootH0P
#print axioms TermRunLoc.runAgreeW3Z_of_G
#print axioms TermRunLoc.runAgreeW3Z_of_K
#print axioms TermRunLoc.runAgreeF3_of_gb2
#print axioms TermRunLoc.runAgreeFT4_gb2_imp_new
#print axioms TermRunLoc.runAgreeF3_of_old
#print axioms TermRunLoc.runAgreeFT4_old_imp_new
#print axioms TermRunLoc.runAgreeF3_of_gb
#print axioms TermRunLoc.runAgreeFT4_gb_imp_new
#print axioms TermRunLoc.iniLoc_mono
#print axioms TermRunLoc.runAgreeF3K_of_F3
#print axioms TermRunLoc.runAgreeT3K_of_T3
#print axioms TermRunLoc.runAgreeF2_of
#print axioms TermRunLoc.runAgreeT2_of
#print axioms TermRunLoc.runAgreeFT3_of
