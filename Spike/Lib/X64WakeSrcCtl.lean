/-
**The source-control premises at main's clone, discharged once** (x86-64):
the facts of main's source at `spawnTerm` (`WakeBoxW.SpawnSrc`) and of the
layout that `WakeBoxW.hB_box`, `wc_main`'s fence and the refusal path take.

- `spawnSrc_ctl` (`hSctl`, `hrun`), `new_ctl` (the start's `hc0`): no `ret`
  and `RunWf`, vacuously: no frame step at a spawn or a `new`.
- `placedSE_of_tbl`: **the generic placement**: `PlacedSE` at no frames from
  a table of word places per source variable, total on the term's free
  variables, each place representing its word, each immediate the layout's.
  Per-node `hpl` (`BlkW (fun s c => PlacedSE …) …`) are instances.
- `placedSE_spawnAt`: at `SpawnSrc l`, `c` and `p` at any two places;
  `placedSE_spawn` at `%r12`/`%rbx`, `placedSE_clone` at `CloneInv`,
  `placedSE_ret` at the clone's refused return (`abi.ret` writes `%rax`,
  `%rcx`, `%r11`).
- `placedSE_blkMS`, `placedSE_nodeMS` (with `keepsSlot`, `keeps_fN`): on the
  refusal path (`fN`'s `je`, `x22`, `fl` blocks, its `ts` node), at main's
  slots `-16`, `-8` (`MS`); `placedSE_stubBlk`, `placedSE_stubNode`: in the
  threads abort's callee (`StubTW`'s nodes), the slots as at the call
  (`fE`'s `σC`).
- `placeVal_slot_abs`, `placeVal_slot_frame`, `placeVal_slot_kept`: a frame
  slot as a `Place.slot` (`Abs`, `DFrame`, across a call).
- `prog_W` (`hprog`), `hna_W` (`hna`): the layout's program is wake's; the
  clone's `syscall` is not the take site (both labels' offsets,
  `codeLabel_base`).

x86-64 twin of `Spike/Lib/A64WakeSrcCtl.lean` (same names, namespace
`Spike.Lib.X64.WakeSrcCtl`).

**Unlike AArch64**:
- `c`'s cell and main's `ThreadId` word are in `%r12`, `%rbx` at the clone
  (A64 `x9`, `x10`), and in main's slots `-16`, `-8` on the refusal path
  (A64 `-72`, `-80`); `abi.ret` takes a `BitVec 64` (A64 `Int`);
- the refusal path has a test node `ts` (`NodeW`, `placedSE_nodeMS`) before
  its blocks `je`, `x22` (which stores at `-56`), `fl` (whose `call`
  pushes at `-72`); `keepsSlot` counts `push`/`call` writes;
- the threads abort's callee region is `R.callee (-72 - 8) (-24) 16` and its
  frame condition is the caller's `F` (A64 `R.callee (-80) (-48) 0`, a
  `DFrame`); main's slots at `-64` and above are kept;
- the layout's program is wake's cells (`cellsOf asm`, any assembly `asm`;
  A64 `textProgram SccCertificate.asm`, `wakeProg`), and `labelAddr_add`
  moves `codeLabel` (`codeLabel_base`; A64 `codeOf_base`);
- `new_ctl` restates `Spike.Lib.X64.WakeC0.new_ctl` (on the start's branch).
-/
import Spike.Lib.X64WakeBoxW
import Spike.Lib.X64WakeAWSite
import Spike.Lib.X64WakeSpawnFail
import Spike.Lib.FrameNew

namespace Spike.Lib.X64.WakeSrcCtl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (FrameRun FrameStep Region PlaceWX)
open Spike.Lib.X64 (SO AS AM Abs DFrame CKept ND BlkW NodeW classify arun dstep)
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.X64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakeBoxW (SpawnSrc)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeSrcDefs (spawnTerm mainTidLbl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCode (wakeCells)

/-! ## The source at the spawn -/

/-- **A control at `spawnTerm` takes no frame step** at no frames: the spawn
is a configuration step, no thread step; it is no call, and no frame is
returned into. -/
theorem frameRun_spawn {p : Prog} {c : Ctl} {q : Ctl × List TermRun.Frame}
    (ht : c.term = spawnTerm) (h : FrameRun p (c, []) q) : q = (c, []) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    exfalso
    cases hs with
    | loc h =>
      have := h.2 { p := p, k := default, arch := default, n := 1, i := 0, lbase := 0 } #[] []
        { term := c.term, env := c.env } rfl rfl rfl rfl
      simp [TermRun.tstep, ht, spawnTerm, TermRun.evalOp] at this
    | call hc => rw [ht] at hc; simp [spawnTerm] at hc

/-- **The source premise at `SpawnSrc`** (`hSctl`, `hrun`): not at a `ret`,
and its runs well formed, vacuously: it runs nowhere. -/
theorem spawnSrc_ctl {l : WeakMem.AllocLabel} {c : Ctl} (h : SpawnSrc l c) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf wakeSrc c [] := by
  have ht := h.1
  refine ⟨fun a e => (by rw [ht] at e; simp [spawnTerm] at e), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    cases frameRun_spawn ht hr
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp [spawnTerm] at hc
  · intro c' fs' hr x a τ e hc
    cases frameRun_spawn ht hr
    rw [ht] at hc; simp [spawnTerm] at hc

/-- **The source premise at a box allocation** (the start control, `let o =
new z in …`): not at a `ret`, and its runs well formed, vacuously: a frame run
from a `new` is empty (`FrameRun.eq_of_new`). -/
theorem new_ctl {p : Prog} {c : Ctl} {x : String} {a : CoreTerm.At} {T : Option Ty} {e : Expr}
    (ht : c.term = .let_ x (.new a T) e) : (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
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
`pm`'s (registers at the clone, `%r12`/`%rbx`; main's frame slots on the
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
    rw [ht, show exprFv spawnTerm = ["p", "c"] by decide] at hx
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

/-- **main's source at the spawn placed** at the registers: `c` at `%r12`,
`p` at `%r12` and `%rbx`, given `lbl` puts `l` at `%r12` and main's id at
`%rbx`. -/
theorem placedSE_spawn {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    (hsrc : SpawnSrc l c) (h12 : lbl l = some (regVal s (.r .r12)).toNat)
    (hbx : lbl (mainTidLbl 2) = some (regVal s (.r .rbx)).toNat) : PlacedSE Λ lbl s c [] :=
  placedSE_spawnAt (.reg (.r .r12)) (.reg (.r .rbx)) hsrc ⟨_, rfl, h12⟩ ⟨_, rfl, hbx⟩

/-- **A region cell as a `Place.slot`**: at a state whose machine data is
the abstract state `σ` in `R`, cell `k`'s absolute address reads `σ.slot k`. -/
theorem placeVal_slot_abs {R : Region} {o : SO} {σ : AS} {s : State} (hA : Abs R o s.st.1 σ) {k : Int}
    (hk : R.Off k) : placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, hj, hv]

/-- **A cell outside the region as a `Place.slot`**: memory outside `R` is
as at `m0` (`DFrame`), so an 8-byte word of `m0` there reads the same. -/
theorem placeVal_slot_frame {R : Region} {m0 : MachineData} {s : State} (hF : DFrame R m0 s.st.1)
    {a : BitVec 64} (hfit : a.toNat + 8 ≤ 2 ^ 64)
    (hout : (a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat)
    {j : Int} (hj : Mem.loadInt m0.dmem a 8 = some j) :
    placeVal (machine (kernel 1)) s (.slot a.toNat) = some (BitVec.ofInt 64 j).toNat := by
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 a.toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, hF a hfit hout, hj]

/-! ## main's source on the refusal path -/

/-- **No write of a block hits cell `j`** from static offsets `o`: no store
`mov %r, n(%b)` at `j`, no `push` or `call` pushing at `j` (decided on a
concrete block). -/
def keepsSlot (j : Int) : SO → List (Directive × Nat) → Bool
  | _, [] => true
  | o, (d, _) :: ds =>
    match classify d with
    | some a =>
      (match a with
        | .st b n _ => decide ((o.get b).getD 0 + n.toInt ≠ j)
        | .push _ | .call _ => decide (o.sp - 8 ≠ j)
        | _ => true) && keepsSlot j (a.so o) ds
    | none => keepsSlot j o ds

/-- **A block keeping cell `j` keeps it on every prefix's abstract run.** -/
theorem arun_slot_keep (lab : String → Int64) (j : Int) :
    ∀ (blk : List (Directive × Nat)) (am : AM) (k : Nat), keepsSlot j am.so blk = true →
      (arun lab (blk.take k) am).σ.slot j = am.σ.slot j
  | [], _, k, _ => by simp [arun]
  | _ :: _, am, 0, _ => rfl
  | (d, z) :: ds, am, k + 1, h => by
    simp only [List.take_succ_cons, arun, List.foldl] at h ⊢
    unfold keepsSlot at h
    unfold dstep
    split at h <;> rename_i heq <;> simp only [heq]
    · rename_i a
      simp only [Bool.and_eq_true] at h
      refine (arun_slot_keep lab j ds _ k h.2).trans ?_
      cases a <;> simp_all [Spike.Lib.X64.AI.step, Spike.Lib.upd_apply] <;> exact fun e => absurd e.symm h.1
    · exact arun_slot_keep lab j ds am k h

open Spike.Lib.X64.WakePh.SpawnFail (MS) in
/-- **Placed on a refusal block in main's frame** (`fN`'s `je`, `x22`,
`fl`): the source at `cP` and main's slots `MS cA mT` at the node, kept by
the block, `lbl` putting `l` at `cA` and main's id at `mT`. -/
theorem placedSE_blkMS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP : Ctl} {cA mT : BitVec 64}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} (hsrc : SpawnSrc l cP)
    (h16 : R.Off (-16)) (h8 : R.Off (-8)) (hJ : ∀ σ c, n.J σ c → c = cP ∧ MS cA mT σ)
    (hk : keepsSlot (-16) n.o blk = true ∧ keepsSlot (-8) n.o blk = true)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨rfl, h1, h2⟩ := hJ σ c hj
  refine ⟨placedSE_spawnAt (.slot (R.addr (-16)).toNat) (.slot (R.addr (-8)).toNat) hsrc
    ⟨_, placeVal_slot_abs hA h16, ?_⟩ ⟨_, placeVal_slot_abs hA h8, ?_⟩, fun _ h => h⟩
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.1, h1]; exact hlc
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.2, h2]; exact hlm

open Spike.Lib.X64.WakePh.SpawnFail (MS) in
/-- **Placed at a refusal node in main's frame** (`fN`'s `ts`): the source
at `cP` and main's slots `MS cA mT` at the node. -/
theorem placedSE_nodeMS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP : Ctl}
    {cA mT : BitVec 64} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} (hsrc : SpawnSrc l cP) (h16 : R.Off (-16)) (h8 : R.Off (-8))
    (hJ : ∀ σ c, n.J σ c → c = cP ∧ MS cA mT σ) (hlc : lbl l = some cA.toNat)
    (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n := by
  intro s c ⟨_, _, _, _, σ, hA, _, hj⟩
  obtain ⟨rfl, h1, h2⟩ := hJ σ c hj
  exact ⟨placedSE_spawnAt _ _ hsrc ⟨_, placeVal_slot_abs hA h16, by rw [h1]; exact hlc⟩
    ⟨_, placeVal_slot_abs hA h8, by rw [h2]; exact hlm⟩, fun _ h => h⟩

/-- The refusal blocks keep main's slots `-16`, `-8` (`x22` stores at
`-56`, `fl`'s `call` pushes at `-72`). -/
theorem keeps_fN : ∀ blk ∈ [Spike.Lib.X64.WakePh.Parent.jeB, Spike.Lib.X64.WakePh.Parent.x22B,
    Spike.Lib.X64.WakePh.SpawnFail.flB],
    keepsSlot (-16) Spike.Lib.X64.WakePh.WcClone.oW blk = true ∧
      keepsSlot (-8) Spike.Lib.X64.WakePh.WcClone.oW blk = true := by
  decide +kernel

/-- **main's slot across a call**: below the callee's region (`R.callee
(-72 - 8) (-24) 16`), a cell of main's frame `R` at `-64` or above is as at
the call (`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_kept {R : Region} {o : SO} {m0 m' : MachineData} {σC : AS} {s : State}
    (hA : Abs R o m0 σC) (hK : CKept R (-72 - 8) (-24) 16 m0 m')
    (hD : DFrame (R.callee (-72 - 8) (-24) 16) m' s.st.1) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 16 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -64 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-72 - 8) (-24) 16).Off (k - (-72 - 8)) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h80 := Region.addr_toNat_of hR (k := -72 - 8) (by omega) (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, e, hK k hk hc, hj, hv]

open Spike.Lib.X64.WakePh.SpawnFail (fE) in
/-- **Placed in the threads abort's callee** (`StubTW`'s nodes below main's
frame): at the call `fE`'s `σC` pins main's slots, which the callee keeps. -/
theorem placedSE_stub {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP c0 c : Ctl}
    {cA mT : BitVec 64} {lab : String → Int64} {R : Region} {F : MachineData → Prop} {o : SO}
    {m0 m' : MachineData} {σC : AS} {s : State} (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 16 ≤ R.hi) (hE : (fE lab cP cA mT).J σC c0)
    (hF : F m' ∧ CKept R (-72 - 8) (-24) 16 m0 m' ∧ Abs R o m0 σC)
    (hD : DFrame (R.callee (-72 - 8) (-24) 16) m' s.st.1) (hc : c = c0)
    (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) : PlacedSE Λ lbl s c [] := by
  obtain ⟨hc0, -, -, h1, h2⟩ := hE
  have h16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have h8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  subst hc hc0
  exact placedSE_spawnAt _ _ hsrc
    ⟨_, placeVal_slot_kept hF.2.2 hF.2.1 hD hR hlo hhi h16 (by omega), by rw [h1]; exact hlc⟩
    ⟨_, placeVal_slot_kept hF.2.2 hF.2.1 hD hR hlo hhi h8 (by omega), by rw [h2]; exact hlm⟩

section Stub

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {cP c0 : Ctl} {cA mT : BitVec 64}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {m0 : MachineData}
  {σC : AS} {n : ND}

set_option hygiene false in
/-- The callee's frame condition at the call (`seg_spawnFailW`'s `hstub`). -/
local notation "FC" => fun m => F m ∧ CKept R (-72 - 8) (-24) 16 m0 m ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m0 σC

set_option hygiene false in
/-- The call's node invariant (`fE`'s at `σC`, `c0`). -/
local notation "HE" => (Spike.Lib.X64.WakePh.SpawnFail.fE (_root_.Executable.labels exe).label cP cA mT).J σC c0

/-- `placedSE_stub` at a block node of the callee (`BlkW`, the node's
invariant pinning the source at `c0`). -/
theorem placedSE_stubBlk {blk : List (Directive × Nat)} (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80)
    (hhi : 16 ≤ R.hi) (hE : HE) (hc : ∀ σ c, n.J σ c → c = c0) (hlc : lbl l = some cA.toNat)
    (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-72 - 8) (-24) 16)
      FC n blk :=
  fun _ σ c _ _ _ _ _ hF hj _ _ _ _ hD =>
    ⟨placedSE_stub hsrc hR hlo hhi hE hF hD (hc σ c hj) hlc hlm, fun _ h => h⟩

/-- `placedSE_stub` at a node of the callee (`NodeW`). -/
theorem placedSE_stubNode (hsrc : SpawnSrc l cP) (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hE : HE)
    (hc : ∀ σ c, n.J σ c → c = c0) (hlc : lbl l = some cA.toNat) (hlm : lbl (mainTidLbl 2) = some mT.toNat) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee (-72 - 8) (-24) 16)
      FC n :=
  fun _ c ⟨_, _, _, _, σ, _, hF, hj⟩ =>
    ⟨placedSE_stub hsrc hR hlo hhi hE hF (DFrame.refl _ _) (hc σ c hj) hlc hlm, fun _ h => h⟩

end Stub

/-- **Placed at the clone's `syscall`** (`CloneInv`, the source at
`SpawnSrc l`): `CloneInv`'s labels put `c`'s label at `%r12` and main's id at
`%rbx`. -/
theorem placedSE_clone {L : RuntimeLayout} {endPc : Int64} {lbl : Lbl} {s : State} {c : Ctl}
    {l : WeakMem.AllocLabel} (hci : Spike.Lib.X64.Flow.WakeWc.CloneInv L endPc lbl s c [])
    (hsrc : SpawnSrc l c) : PlacedSE L.Λ lbl s c [] := by
  obtain ⟨-, J, t, l', -, -, -, hc', -, -, h12, hbx⟩ := hci
  have e : l' = l := by
    have := hsrc.2.2.1; rw [hc'] at this; simpa [TermRun.cst, Promises.TVal.mk0] using this
  subst e
  exact placedSE_spawn hsrc h12 hbx

/-- **Placed at the clone's refused return** (`abi.ret s r`, the
threads-abort path's entry): the return writes `%rax`, `%rcx`, `%r11` only
(`retRegs64`), so `%r12` and `%rbx` are as at the clone. -/
theorem placedSE_ret {L : RuntimeLayout} {endPc : Int64} {lbl : Lbl} {s : State} {c : Ctl}
    {l : WeakMem.AllocLabel} (hci : Spike.Lib.X64.Flow.WakeWc.CloneInv L endPc lbl s c [])
    (hsrc : SpawnSrc l c) (r : BitVec 64) : PlacedSE L.Λ lbl (abi.ret s r) c [] := by
  obtain ⟨-, J, t, l', -, -, -, hc', -, -, h12, hbx⟩ := hci
  have e : l' = l := by
    have := hsrc.2.2.1; rw [hc'] at this; simpa [TermRun.cst, Promises.TVal.mk0] using this
  subst e
  exact placedSE_spawn hsrc h12 hbx

/-! ## The layout's facts -/

/-- **A label's address moves with the base.** -/
theorem labelAddr_add {D : Type} (lb : D → Option String) (sz : D → Nat) (l : String) :
    ∀ (ds : List D) (a b : Nat), labelAddr lb sz (a + b) l ds = (labelAddr lb sz b l ds).map (a + ·)
  | [], _, _ => rfl
  | d :: ds, a, b => by
    simp only [labelAddr]
    split
    · rfl
    · rw [Nat.add_assoc]; exact labelAddr_add lb sz l ds a (b + sz d)

/-- `codeLabel` at a base is `codeLabel` at `0` moved by the base. -/
theorem codeLabel_base (b : Nat) (cells : List (Directive × Nat)) (l : String) :
    codeLabel b cells l = (codeLabel 0 cells l).map (b + ·) := by
  unfold codeLabel; simpa using labelAddr_add (fun c : Directive × Nat => labelName c.1) (·.2) l cells b 0

/-- `.Lwc_main.x3` in wake's cells at `0` (the clone's `syscall` is 46 bytes
past it). -/
theorem codeLabel_x21 : codeLabel 0 wakeCells Spike.Lib.X64.WakePh.WcClone.x21L = some 5035 := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- The take site in wake's cells at `0`. -/
theorem codeLabel_site : codeLabel 0 wakeCells Spike.Lib.X64.Flow.Ret0.StackTake.siteL = some 1877 := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- Wake's cells' total size. -/
theorem wakeCells_size : (wakeCells.map (·.2)).sum = 5217 := by decide +kernel

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The output's program is wake's**: both are the cells of one assembly. -/
theorem oprog_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) :
    o.prog = wakeCells :=
  Option.some.inj (hpa.symm.trans hwp)

/-- **The layout's program is wake's** (`hB_box`'s `hprog`). -/
theorem prog_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) :
    (Ly).prog = wakeCells :=
  oprog_W hpa hwp

include hp in
/-- **The clone's `syscall` is not the take site** in the layout, both
labels resolved in wake's cells (`hlab_ofPlaceWX`) at offsets that differ. -/
theorem cloneAt_ne_site (ho : o.prog = wakeCells) :
    (Spike.Lib.X64WakePreA.cloneAt (Ly).exe).toBitVec.toNat ≠
      ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have h1 := PlaceWX.hlab_ofPlaceWX hp i Spike.Lib.X64.WakePh.WcClone.x21L ((Ly).Λ.code.lo + 5035)
    (by rw [ho, codeLabel_base, codeLabel_x21]; rfl)
  have h2 := PlaceWX.lab_toNat hp i (l := Spike.Lib.X64.Flow.Ret0.StackTake.siteL)
    (a := (Ly).Λ.code.lo + 1877) (by rw [ho, codeLabel_base, codeLabel_site]; rfl)
  have hend := PlaceWX.codeEnd_lt hp i
  rw [ho] at hend; unfold Scc.Sem.X64.codeEnd at hend; rw [wakeCells_size] at hend
  unfold Spike.Lib.X64WakePreA.cloneAt
  change ((Ly).lab Spike.Lib.X64.WakePh.WcClone.x21L + Int64.ofNat 46).toBitVec.toNat ≠ _
  rw [h1, h2, Spike.Lib.X64.Rt.PhOfTab.toNat_add]
  omega

/-- **`hB_box`'s `hna`**: the clone's `syscall` is not `aW`, the take site
(`aW_site`). -/
theorem hna_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (E : Entry) :
    (Spike.Lib.X64WakePreA.cloneAt (Ly).exe).toBitVec.toNat ≠ (X64WakeOSide.aW hp i E).toBitVec.toNat := by
  rw [X64WakeOSide.aW_site hp i hpa E]
  exact cloneAt_ne_site hp i (oprog_W hpa hwp)

end Place

end Spike.Lib.X64.WakeSrcCtl

/-- info: 'Spike.Lib.X64.WakeSrcCtl.frameRun_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.frameRun_spawn

/-- info: 'Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.spawnSrc_ctl

/-- info: 'Spike.Lib.X64.WakeSrcCtl.new_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.new_ctl

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_of_tbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_of_tbl

/-- info: 'Spike.Lib.X64.WakeSrcCtl.rep_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.rep_at

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_spawnAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_spawnAt

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_spawn

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placeVal_slot_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placeVal_slot_abs

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placeVal_slot_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placeVal_slot_frame

/-- info: 'Spike.Lib.X64.WakeSrcCtl.arun_slot_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.arun_slot_keep

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_blkMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_blkMS

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_nodeMS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_nodeMS

/-- info: 'Spike.Lib.X64.WakeSrcCtl.keeps_fN' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.keeps_fN

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placeVal_slot_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placeVal_slot_kept

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_stub

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_stubBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_stubBlk

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_stubNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_stubNode

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_clone

/-- info: 'Spike.Lib.X64.WakeSrcCtl.placedSE_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.placedSE_ret

/-- info: 'Spike.Lib.X64.WakeSrcCtl.labelAddr_add' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.labelAddr_add

/-- info: 'Spike.Lib.X64.WakeSrcCtl.codeLabel_base' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.codeLabel_base

/-- info: 'Spike.Lib.X64.WakeSrcCtl.codeLabel_x21' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.codeLabel_x21

/-- info: 'Spike.Lib.X64.WakeSrcCtl.codeLabel_site' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.codeLabel_site

/-- info: 'Spike.Lib.X64.WakeSrcCtl.wakeCells_size' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.wakeCells_size

/-- info: 'Spike.Lib.X64.WakeSrcCtl.oprog_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.oprog_W

/-- info: 'Spike.Lib.X64.WakeSrcCtl.prog_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.prog_W

/-- info: 'Spike.Lib.X64.WakeSrcCtl.cloneAt_ne_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.cloneAt_ne_site

/-- info: 'Spike.Lib.X64.WakeSrcCtl.hna_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeSrcCtl.hna_W
