/-
**The source-control premises at main's clone, discharged once** (AArch64):
the facts of main's source at `spawnTerm` (`WakeBoxW.SpawnSrc`) and of the
layout that `WakeBoxW.hB_box`, `wc_main`'s fence and the refusal path take.

- `spawnSrc_ctl` (`hSctl`, `hrun`), `new_ctl` (the start's `hc0`): no `ret`
  and `RunWf`, vacuously: no frame step at a spawn or a `new`.
- `placedSE_of_tbl`: **the generic placement**: `PlacedSE` at no frames from
  a table of word places per source variable, total on the term's free
  variables, each place representing its word, each immediate the layout's.
  Per-node `hpl` (`BlkW (fun s c => PlacedSE …) …`) are instances.
- `placedSE_spawnAt`: at `SpawnSrc l`, `c` and `p` at any two places;
  `placedSE_spawn` at `x9`/`x10`, `placedSE_clone` at `CloneInv`,
  `placedSE_ret` at the clone's refused return (`abi.ret` writes `x0`).
- `placedSE_blkMS` (with `keepsSlot`, `keeps_fN`): on the refusal blocks
  (`fN`'s `cb`, `cl`, `fl`), at main's slots `-72`, `-80` (`MS`);
  `placedSE_stubBlk`, `placedSE_stubNode`: in the threads abort's callee
  (`StubTW`'s nodes), the slots as at the call (`fE`'s `σC`).
- `placeVal_slot_abs`, `placeVal_slot_frame`, `placeVal_slot_kept`: a frame
  slot as a `Place.slot` (`Abs`, `DFrame`, across a call).
- `prog_W` (`hprog`), `hna_W` (`hna`): the layout's program is wake's; the
  clone's `svc` is not the take site (both labels' offsets).
-/
import Spike.Lib.A64WakeBoxW
import Spike.Lib.WakeAWSite
import Spike.Lib.A64SiteOfPlaceW
import Spike.Lib.FrameNew
import Spike.Lib.A64WakeSpawnFail

namespace Spike.Lib.WakeSrcCtl

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (FrameRun FrameStep)
open Spike.Lib.A64Consumer (Lbl Placed)
open Spike.Lib.A64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.WakeBoxW (SpawnSrc)
open Spike.Lib.WakeT1 (wakeSrc mainTidLbl)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)

/-! ## The source at the spawn -/

/-- **A control at `spawnTerm` takes no frame step** at no frames: the spawn
is a configuration step, no thread step; it is no call, and no frame is
returned into. -/
theorem frameRun_spawn {p : Prog} {c : Ctl} {q : Ctl × List TermRun.Frame}
    (ht : c.term = Spike.Lib.WakePreA.spawnTerm) (h : FrameRun p (c, []) q) : q = (c, []) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    exfalso
    cases hs with
    | loc h =>
      have := h.2 { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
        { term := c.term, env := c.env } rfl rfl rfl rfl
      simp [TermRun.tstep, ht, Spike.Lib.WakePreA.spawnTerm, TermRun.evalOp] at this
    | call hc => rw [ht] at hc; simp [Spike.Lib.WakePreA.spawnTerm] at hc

/-- **The source premise at `SpawnSrc`** (`hSctl`, `hrun`): not at a `ret`,
and its runs well formed, vacuously: it runs nowhere. -/
theorem spawnSrc_ctl {l : WeakMem.AllocLabel} {c : Ctl} (h : SpawnSrc l c) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [] := by
  have ht := h.1
  refine ⟨fun a e => (by rw [ht] at e; simp [Spike.Lib.WakePreA.spawnTerm] at e), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    cases frameRun_spawn ht hr
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp [Spike.Lib.WakePreA.spawnTerm] at hc
  · intro c' fs' hr x a τ e hc
    cases frameRun_spawn ht hr
    rw [ht] at hc; simp [Spike.Lib.WakePreA.spawnTerm] at hc

/-- **The source premise at a box allocation** (the start control, `let o =
new z in …`): not at a `ret`, and its runs well formed, vacuously: a frame run
from a `new` is empty (`FrameRun.eq_of_new`). -/
theorem new_ctl {p : Prog} {c : Ctl} {x : String} {a : At} {e : Expr} (ht : c.term = .let_ x (.new a) e) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  refine ⟨fun a' h => (by rw [ht] at h; cases h), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x' a' e' ty w hc
    cases Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp at hc
  · intro c' fs' hr x' a' τ e' hc
    cases Spike.Lib.FrameNew.FrameRun.eq_of_new hr ht
    rw [ht] at hc; simp at hc

/-! ## The generic placement -/

/-- A word-place table: per source variable, its words' places. -/
abbrev Tbl := List (String × List (WordPlace (machine (kernel 1)).I.RegId))

/-- **A control placed by a table** at no frames: every free variable's
words have places in `tbl` (`htot`), each place represents its word in `s`
(`hrep`), each immediate is the layout's at the control's term (`himm`). -/
theorem placedSE_of_tbl {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} (tbl : Tbl)
    (htot : ∀ x ∈ exprFv c.term, ∀ ty ws, TermRun.lookupE c.env x = some (ty, ws) →
      ∃ pls, tbl.lookup x = some pls ∧ ws.length ≤ pls.length)
    (hrep : ∀ x pls ty ws, tbl.lookup x = some pls → TermRun.lookupE c.env x = some (ty, ws) →
      ∀ (k : Nat) wp (wd : TermRun.Word), pls[k]? = some wp → ws[k]? = some wd →
        WordPlaceRep (machine (kernel 1)) lbl s wp wd.val)
    (himm : ∀ x pls k n, tbl.lookup x = some pls → pls[k]? = some (.imm n) → Λ.imms c.term x k = some n) :
    PlacedSE Λ lbl s c [] := by
  refine .inl (PlacedS.ofNil ⟨fun x k => (tbl.lookup x).bind (·[k]?), ?_, ?_, ?_⟩)
  · intro x ty ws hl k wd wp hwd hwp
    cases h : tbl.lookup x with
    | none => simp [h] at hwp
    | some pls => simp only [h, Option.bind_some] at hwp; exact hrep x pls ty ws h hl k wp wd hwp hwd
  · intro x hx ty ws hl k hk
    obtain ⟨pls, h, hle⟩ := htot x hx ty ws hl
    exact ⟨pls[k], by simp [h, List.getElem?_eq_getElem (show k < pls.length by omega)]⟩
  · intro x k n hn
    cases h : tbl.lookup x with
    | none => simp [h] at hn
    | some pls => simp only [h, Option.bind_some] at hn; exact himm x pls k n h hn

/-! ## main's source at its clone -/

/-- A locative word of `l` is represented at a place holding `l`'s base. -/
theorem rep_at {lbl : Lbl} {s : State} {l : WeakMem.AllocLabel} {pl : Place (machine (kernel 1)).I.RegId}
    (h : ∃ v, placeVal (machine (kernel 1)) s pl = some v ∧ lbl l = some v) :
    WordPlaceRep (machine (kernel 1)) lbl s (.one pl) (TermRun.cst (.loc ⟨l, 0⟩ 0)).val := by
  obtain ⟨v, hv, hl⟩ := h
  exact ⟨v, hv, by decide, v, by simp [Scc.Sem.wordAddr, hl], by simp⟩

/-- **main's source at the spawn placed at any two places**: `c` at `pc`,
`p` at `pc` and `pm`, given `lbl` puts `l` at `pc`'s word and main's id at
`pm`'s (registers at the clone, `x9`/`x10`; main's frame slots on the
refusal path, where the registers are reused). -/
theorem placedSE_spawnAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    (pc pm : Place (machine (kernel 1)).I.RegId) (hsrc : SpawnSrc l c)
    (h9 : ∃ v, placeVal (machine (kernel 1)) s pc = some v ∧ lbl l = some v)
    (h10 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  obtain ⟨ht, -, hc, -, hpp⟩ := hsrc
  simp only [TermRun.evalAt] at hc hpp
  refine placedSE_of_tbl [("c", [.one pc]), ("p", [.one pc, .one pm])] ?_ ?_ ?_
  · intro x hx ty ws hl
    rw [ht, show exprFv Spike.Lib.WakePreA.spawnTerm = ["p", "c"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [hpp] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hc] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty ws hpl hl k wp wd hwp hwd
    by_cases ex : x = "c"
    · subst ex; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hc] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h9
    by_cases ep : x = "p"
    · subst ep; simp [List.lookup] at hpl; subst hpl
      rw [hpp] at hl; cases hl
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h9
      | 1, hwp, hwd => cases hwp; cases hwd; exact rep_at h10
    · simp [List.lookup, beq_false_of_ne ex, beq_false_of_ne ep] at hpl
  · intro x pls k n hpl hn'
    by_cases ex : x = "c"
    · subst ex; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases ep : x = "p"
    · subst ep; simp [List.lookup] at hpl; subst hpl
      match k, hn' with
      | 0, hn' => cases hn'
      | 1, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ex, beq_false_of_ne ep] at hpl

/-- **main's source at the spawn placed** at the registers: `c` at `x9`,
`p` at `x9` and `x10`, given `lbl` puts `l` at `x9` and main's id at `x10`. -/
theorem placedSE_spawn {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    (hsrc : SpawnSrc l c) (h9 : lbl l = some (regVal s (.x 9)).toNat)
    (h10 : lbl (mainTidLbl 2) = some (regVal s (.x 10)).toNat) : PlacedSE Λ lbl s c [] :=
  placedSE_spawnAt (.reg (.x 9)) (.reg (.x 10)) hsrc ⟨_, rfl, h9⟩ ⟨_, rfl, h10⟩

/-- **A region cell as a `Place.slot`**: at a state whose machine data is
the abstract state `σ` in `R`, cell `k`'s absolute address reads `σ.slot k`. -/
theorem placeVal_slot_abs {R : Spike.Lib.Region} {o : Spike.Lib.A64.Flow.SO} {σ : Spike.Lib.A64.Flow.AS}
    {s : State} (hA : Spike.Lib.A64.Flow.Abs R o s.st.1 σ) {k : Int} (hk : R.Off k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, hj, hv]

/-- **A cell outside the region as a `Place.slot`**: memory outside `R` is
as at `m0` (`DFrame`), so an 8-byte word of `m0` there reads the same. -/
theorem placeVal_slot_frame {R : Spike.Lib.Region} {m0 : MachineData} {s : State}
    (hF : Spike.Lib.A64.Flow.DFrame R m0 s.st.1) {a : BitVec 64} (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat)
    {j : Int} (hj : Mem.loadInt m0.dmem a 8 = some j) :
    placeVal (machine (kernel 1)) s (.slot a.toNat) = some (BitVec.ofInt 64 j).toNat := by
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, hF a hfit hout, hj]

/-! ## main's source on the refusal path -/

/-- **No store of a block writes cell `j`** from static offsets `o`
(decided on a concrete block). -/
def keepsSlot (j : Int) : Spike.Lib.A64.Flow.SO → List Directive → Bool
  | _, [] => true
  | o, d :: ds =>
    match Spike.Lib.A64.Flow.classify d with
    | some a => (match a with | .str _ n => decide (o.sp + n.toInt ≠ j) | _ => true) &&
        keepsSlot j (a.so o) ds
    | none => keepsSlot j o ds

/-- **A block keeping cell `j` keeps it on every prefix's abstract run.** -/
theorem arun_slot_keep (lab : Label → Int64) (j : Int) :
    ∀ (blk : List Directive) (am : Spike.Lib.A64.Flow.AM) (k : Nat), keepsSlot j am.so blk = true →
      (Spike.Lib.A64.Flow.arun lab (blk.take k) am).σ.slot j = am.σ.slot j
  | [], _, k, _ => by simp [Spike.Lib.A64.Flow.arun]
  | d :: ds, am, 0, _ => rfl
  | d :: ds, am, k + 1, h => by
    simp only [List.take_succ_cons, Spike.Lib.A64.Flow.arun, List.foldl] at h ⊢
    unfold keepsSlot at h
    unfold Spike.Lib.A64.Flow.dstep
    split at h <;> rename_i heq <;> simp only [heq]
    · rename_i a
      simp only [Bool.and_eq_true] at h
      refine (arun_slot_keep lab j ds _ k h.2).trans ?_
      cases a <;> simp_all [Spike.Lib.A64.Flow.AI.step, Spike.Lib.upd_apply]
      exact fun e => absurd e.symm h.1
    · exact arun_slot_keep lab j ds am k h

open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (MS) in
/-- **Placed on a refusal block in main's frame** (`fN`'s `cb`, `cl`,
`fl`): the source at `cP` and main's slots `MS cA mT` at the node, kept by
the block, `lbl` putting `l` at `cA` and main's id at `mT`. -/
theorem placedSE_blkMS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP : Ctl} {cA mT : BitVec 64}
    {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : Spike.Lib.A64.Flow.ND} {blk : List Directive} (hsrc : SpawnSrc l cP)
    (h72 : R.Off (-72)) (h80 : R.Off (-80)) (hJ : ∀ σ c, n.J σ c → c = cP ∧ MS cA mT σ)
    (hk : keepsSlot (-72) n.o blk = true ∧ keepsSlot (-80) n.o blk = true)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    Spike.Lib.A64.Flow.BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨rfl, h1, h2⟩ := hJ σ c hj
  refine ⟨placedSE_spawnAt (.slot (R.addr (-72)).toNat) (.slot (R.addr (-80)).toNat) hsrc
    ⟨_, placeVal_slot_abs hA h72, ?_⟩ ⟨_, placeVal_slot_abs hA h80, ?_⟩, fun _ h => h⟩
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.1, h1]; exact hlc
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.2, h2]; exact hlm

/-- The refusal blocks keep main's slots `-72`, `-80` (`cl` stores at `-32`). -/
theorem keeps_fN : ∀ blk ∈ [Spike.Lib.A64.Flow.Worker.Wake.Child.cb Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM,
    Spike.Lib.A64.Flow.Worker.Wake.Parent.cl Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM,
    Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.flB],
    keepsSlot (-72) Spike.Lib.A64.Flow.Worker.Wake.Parent.oP blk = true ∧
      keepsSlot (-80) Spike.Lib.A64.Flow.Worker.Wake.Parent.oP blk = true := by
  decide +kernel

/-- **main's slot across a call**: below the callee's region (`R.callee
(-80) (-48) 0`), a cell of main's frame `R` at `-80` or above is as at the
call (`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_kept {R : Spike.Lib.Region} {o : Spike.Lib.A64.Flow.SO} {m1 m' : MachineData}
    {σC : Spike.Lib.A64.Flow.AS} {s : State} (hA : Spike.Lib.A64.Flow.Abs R o m1 σC)
    (hK : Spike.Lib.A64.Flow.CKept R (-80) (-48) 0 m1 m')
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-80) (-48) 0) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -80 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-80) (-48) 0).Off (k - -80) := fun ⟨_, _, h3⟩ => by
    simp only [Spike.Lib.Region.callee] at h3; omega
  have h80 := Spike.Lib.Region.addr_toNat_of hR (k := -80) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Spike.Lib.Region.callee]; omega))
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hK k hk hc, hj, hv]

open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (fE) in
/-- **Placed in the threads abort's callee** (`StubTW`'s nodes below main's
frame): at the call `fE`'s `σC` pins main's slots, which the callee keeps. -/
theorem placedSE_stub {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP c0 c : Ctl}
    {cA mT : BitVec 64} {lab : Label → Int64} {R : Spike.Lib.Region} {m0 m1 m' : MachineData}
    {σC : Spike.Lib.A64.Flow.AS} {s : State} (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hE : (fE Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM lab cP cA mT).J σC c0)
    (hF : Spike.Lib.A64.Flow.DFrame R m0 m' ∧ Spike.Lib.A64.Flow.CKept R (-80) (-48) 0 m1 m' ∧
      Spike.Lib.A64.Flow.Abs R Spike.Lib.A64.Flow.Worker.Wake.Parent.oP m1 σC)
    (hD : Spike.Lib.A64.Flow.DFrame (R.callee (-80) (-48) 0) m' s.st.1) (hc : c = c0)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) : PlacedSE Λ lbl s c [] := by
  obtain ⟨hc0, -, -, h1, h2⟩ := hE
  have h72 : R.Off (-72) := ⟨by decide, by omega, by omega⟩
  have h80 : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  subst hc hc0
  exact placedSE_spawnAt _ _ hsrc
    ⟨_, placeVal_slot_kept hF.2.2 hF.2.1 hD hR hlo hhi h72 (by omega), by rw [h1]; exact hlc⟩
    ⟨_, placeVal_slot_kept hF.2.2 hF.2.1 hD hR hlo hhi h80 (by omega), by rw [h2]; exact hlm⟩

section Stub

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP c0 : Ctl} {cA mT : BitVec 64}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {m0 m1 : MachineData}
  {σC : Spike.Lib.A64.Flow.AS} {n : Spike.Lib.A64.Flow.ND}

set_option hygiene false in
/-- The callee's frame condition at the call (`RefObl`'s). -/
local notation "FC" => fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧ Spike.Lib.A64.Flow.CKept R (-80) (-48) 0 m1 m ∧
  Spike.Lib.A64.Flow.Abs R Spike.Lib.A64.Flow.Worker.Wake.Parent.oP m1 σC

set_option hygiene false in
/-- The call's node invariant (`fE`'s at `σC`, `c0`). -/
local notation "HE" => (Spike.Lib.A64.Flow.Worker.Wake.SpawnFail.fE Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM
  (_root_.Executable.labels exe).label cP cA mT).J σC c0

/-- `placedSE_stub` at a block node of the callee (`BlkW`, the node's
invariant pinning the source at `c0`). -/
theorem placedSE_stubBlk {blk : List Directive} (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hE : HE) (hc : ∀ σ c, n.J σ c → c = c0) (hlc : lbl l = some cA.toNat)
    (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    Spike.Lib.A64.Flow.BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-80) (-48) 0)
      FC n blk :=
  fun _ σ c _ _ _ _ _ hF hj _ _ _ _ hD =>
    ⟨placedSE_stub hsrc hR hlo hhi hE hF hD (hc σ c hj) hlc hlm, fun _ h => h⟩

/-- `placedSE_stub` at a node of the callee (`NodeW`). -/
theorem placedSE_stubNode (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hE : HE)
    (hc : ∀ σ c, n.J σ c → c = c0) (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    Spike.Lib.A64.Flow.NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-80) (-48) 0)
      FC n :=
  fun _ c ⟨_, _, _, _, σ, _, hF, hj⟩ =>
    ⟨placedSE_stub hsrc hR hlo hhi hE hF (Spike.Lib.A64.Flow.DFrame.refl _ _) (hc σ c hj) hlc hlm, fun _ h => h⟩

end Stub

/-- **Placed at the clone's `svc`** (`CloneInv`, the source at `SpawnSrc l`):
`CloneInv`'s labels put `c`'s label at `x9` and main's id at `x10`. -/
theorem placedSE_clone {L : RuntimeLayout} {endPc : Int64} {lbl : Lbl} {s : State} {c : Ctl}
    {l : WeakMem.AllocLabel} (hci : Spike.Lib.A64.Flow.WakeWc.CloneInv L endPc lbl s c [])
    (hsrc : SpawnSrc l c) : PlacedSE L.Λ lbl s c [] := by
  obtain ⟨-, J, t, l', -, -, -, hc', -, -, h9, h10⟩ := hci
  have e : l' = l := by
    have := hsrc.2.2.1; rw [hc'] at this; simpa [TermRun.cst, Promises.TVal.mk0] using this
  subst e
  exact placedSE_spawn hsrc h9 h10

/-- **Placed at the clone's refused return** (`abi.ret s r`, the
threads-abort path's entry): the return writes `x0` only, so `x9` and `x10`
are as at the clone. -/
theorem placedSE_ret {L : RuntimeLayout} {endPc : Int64} {lbl : Lbl} {s : State} {c : Ctl}
    {l : WeakMem.AllocLabel} (hci : Spike.Lib.A64.Flow.WakeWc.CloneInv L endPc lbl s c [])
    (hsrc : SpawnSrc l c) (r : Int) : PlacedSE L.Λ lbl (abi.ret s r) c [] := by
  obtain ⟨-, J, t, l', -, -, -, hc', -, -, h9, h10⟩ := hci
  have e : l' = l := by
    have := hsrc.2.2.1; rw [hc'] at this; simpa [TermRun.cst, Promises.TVal.mk0] using this
  subst e
  exact placedSE_spawn hsrc h9 h10

/-! ## The layout's facts -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **The output's program is wake's**: both parse wake's listing. -/
theorem oprog_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) : o.prog = wakeProg :=
  Except.ok.inj (hpa.symm.trans hwp)

/-- **The layout's program is wake's** (`hB_box`'s `hprog`). -/
theorem prog_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) : (Ly).prog = wakeProg :=
  oprog_W hpa hwp

/-- **A label's address moves with the base.** -/
theorem labelAddr_add {D : Type} (lb : D → Option String) (sz : D → Nat) (l : String) :
    ∀ (ds : List D) (a b : Nat), labelAddr lb sz (a + b) l ds = (labelAddr lb sz b l ds).map (a + ·)
  | [], _, _ => rfl
  | d :: ds, a, b => by
    simp only [labelAddr]
    split
    · rfl
    · rw [Nat.add_assoc]; exact labelAddr_add lb sz l ds a (b + sz d)

/-- `codeOf` at a base is `codeOf` at `0` moved by the base. -/
theorem codeOf_base (b : Nat) (prog : _root_.Program) (l : String) :
    codeOf b prog l = (codeOf 0 prog l).map (b + ·) := by
  unfold Scc.Cert.Link.A64.codeOf; simpa using labelAddr_add Scc.Sem.A64.labelName Directive.fakeSize l prog b 0

/-- The clone's `svc` (13 instructions past `.sp6`) in wake's program at `0`. -/
theorem codeOf_sp6 : codeOf 0 wakeProg (Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM ++ ".sp6") = some 5244 := by
  decide +kernel

/-- The take site in wake's program at `0`. -/
theorem codeOf_site : codeOf 0 wakeProg Spike.Lib.A64.Flow.Ret0.StackTake.siteL = some 1892 := by
  decide +kernel

include hp in
/-- **The clone's `svc` is not the take site** in the layout, both labels
resolved in wake's program (`hlab_ofPlaceW`) at offsets that differ. -/
theorem cloneAt_ne_site (ho : o.prog = wakeProg) :
    (Spike.Lib.WakePreA.cloneAt Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM (Ly).exe).toBitVec.toNat ≠
      ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have h1 := Spike.Lib.PlaceW.hlab_ofPlaceW hp i _ ((Ly).Λ.code.lo + 5244)
    (by rw [ho, codeOf_base, codeOf_sp6]; rfl)
  have h2 := Spike.Lib.PlaceW.lab_toNat hp i (l := Spike.Lib.A64.Flow.Ret0.StackTake.siteL)
    (a := (Ly).Λ.code.lo + 1892) (by rw [ho, codeOf_base, codeOf_site]; rfl)
  have hend := Spike.Lib.PlaceW.codeEnd_lt hp i
  have hs : (wakeProg.map Directive.fakeSize).sum = 5548 := by decide +kernel
  rw [ho] at hend; unfold Scc.Sem.A64.codeEnd at hend; rw [hs] at hend
  unfold Spike.Lib.WakePreA.cloneAt
  change ((Ly).lab _ + _).toBitVec.toNat ≠ ((Ly).lab _).toBitVec.toNat
  rw [h1, h2, Spike.Lib.A64.Rt.PhOfTab.toNat_add]
  omega

/-- **`hB_box`'s `hna`**: the clone's `svc` is not `aW`, the take site
(`aW_site`, `site_ofPlaceW`). -/
theorem hna_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (E : Entry) :
    (Spike.Lib.WakePreA.cloneAt Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM (Ly).exe).toBitVec.toNat ≠
      (Spike.Lib.WakeOSide.aW hp i E).toBitVec.toNat := by
  rw [Spike.Lib.WakeOSide.aW_site hp i hpa hwp (by rw [prog_W hp i hpa hwp]; exact hwp)
    (Spike.Lib.PlaceW.site_ofPlaceW hp i) E]
  exact cloneAt_ne_site hp i (oprog_W hpa hwp)

end Place

end Spike.Lib.WakeSrcCtl

/-- info: 'Spike.Lib.WakeSrcCtl.spawnSrc_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.spawnSrc_ctl

/-- info: 'Spike.Lib.WakeSrcCtl.new_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.new_ctl

/-- info: 'Spike.Lib.WakeSrcCtl.placedSE_of_tbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.placedSE_of_tbl

/-- info: 'Spike.Lib.WakeSrcCtl.placedSE_spawnAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.placedSE_spawnAt

/-- info: 'Spike.Lib.WakeSrcCtl.placedSE_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.placedSE_ret

/-- info: 'Spike.Lib.WakeSrcCtl.hna_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.hna_W

/-- info: 'Spike.Lib.WakeSrcCtl.placedSE_blkMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.placedSE_blkMS

/-- info: 'Spike.Lib.WakeSrcCtl.keeps_fN' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.keeps_fN

/-- info: 'Spike.Lib.WakeSrcCtl.placedSE_stubBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSrcCtl.placedSE_stubBlk
