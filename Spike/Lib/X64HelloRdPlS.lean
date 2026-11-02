/-
**hello.w's `wc_rodata` placement from the allocator's return, at the setup call's frame** (x86-64; twin of
`Spike/Lib/A64HelloRdPlS.lean`; `RdWfSF.rdPostW_WSHF`'s `hpl` at `fs = [HelloRdCf.frH env]`): every node of
`wc_rodata` from `.x15` is placed (`PlacedSE` at the frame) once each of its seven invariants' controls is one of
rodata's controls past the allocation (`RdCH`) at a label `l` the labels put at `.x15`'s `%rax` (`hC`).

The buffer's base is in `%rax` in `.x15`'s first block (kept by `rpB0`), afterwards in the slot `-16` (`rdFr`;
no block stores to it). The frame's only free variable `me` is a slot of `scc_rt_main`'s frame at or above
`-72` (just past the callee's region), kept by the callee (`CKept`) and outside its region (`DFrame`).

- `placed_of_tbl`: a control placed by a word-place table over its free variables (the `Placed` twin of
  `WakeSrcCtl.placedSE_of_tbl`).
- `RdImms`: the layout's immediates at rodata's terms (`m`, `w0`, `w1`, `sl`'s constant words).
- `RdCH`, `placed_rd`: rodata's controls past the allocation, placed at any place of the buffer's base.
- `placeVal_slot_keptR`: a slot of the caller's frame across the call of `wc_rodata` (region
  `Hello1.mR R`; `WakeSrcCtl.placeVal_slot_kept`'s twin).
- `framesPlaced_frH`, `placedSE_rd`: the frame placed; a control placed at the frame.
- `blkW_plS`, `nodeW_plS`: a node of base slot `-16` placed.
- `rdPostW_plS`: `RdPostW` inside the placement at `[frH env]`.

## Differences from the AArch64 version

- The base arrives in `%rax` (AArch64 `x0`) and is saved at the slot `-16` (AArch64 `-48`), so `off48` and
  `keeps48` are `off16` and `keeps16`; `blkW_plS0` reads `%rax` through `rpB0`'s prefixes evaluated
  concretely (`rpB0_rax`; AArch64's `arun_take_reg` with `keep_blk`).
- `wc_rodata`'s region is `R.callee (-80) (-208) 8` (the return address at its `0`), so the caller's slots
  kept across the call are those at `-72` or above (AArch64 `R.callee (-80) (-208) 0`, slots at `-80` or
  above); the frame condition `Hello1.mF` pins `CKept R (-80) (-208) 8`.
- There is no publish fence: `RdPostW` has seven invariants `Jp Jp' J1 J2 J2' J3 J4` (no `J5`) and nine nodes.
- The source's terms are `X64HelloRodataSrc`'s and its last environments `X64HelloRodataSrc.env5`/`envR`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloRdPostWfSF
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64HelloRdCf
import Spike.Lib.X64WakeMainW
import Spike.Lib.X64Hello1Main
import Spike.Lib.X64HelloRodataSrcRun

namespace Spike.Lib.X64.HelloPh.RdPlS

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Ctl Region)
open Spike.Lib.X64 (SO AS AM Abs DFrame CKept ND BlkW NodeW arun)
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.X64ConsumerS (PlacedSE PlacedS FramesPlaced)
open Spike.Lib.X64.Flow.HelloRd (pN RdPostW)
open Spike.Lib.X64.Flow.Hello1 (mR mF rdFr rpB0 rpB1 rpB2 rpB3 rpB4)
open Spike.Lib.X64HelloRodataSrc
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2 envN bBind envA env1 env2 env3 env4 rdK1_lt rdK2_lt)
open Spike.Lib.X64.WakeSrcCtl (Tbl rep_at keepsSlot arun_slot_keep placeVal_slot_abs)
open Spike.Lib.X64WakeMainW (M1 placeVal_cell placeVal_reg)
open Spike.Lib.X64HelloRdCf (frH)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State}

/-! ## Placement by a table -/

/-- **A control placed by a table**: every free variable's words have places in `tbl` (`htot`), each place of a
free variable represents its word in `s` (`hrep`), each immediate of a free variable is the layout's at the
control's term (`himm`). The variables not free in the term are left unplaced. -/
theorem placed_of_tbl {c : Ctl} (tbl : Tbl)
    (htot : ∀ x ∈ exprFv c.term, ∀ ty ws, lookupE c.env x = some (ty, ws) →
      ∃ pls, tbl.lookup x = some pls ∧ ws.length ≤ pls.length)
    (hrep : ∀ x pls ty ws, tbl.lookup x = some pls → lookupE c.env x = some (ty, ws) →
      ∀ (k : Nat) wp (wd : Word), pls[k]? = some wp → ws[k]? = some wd → WordPlaceRep M1 lbl s wp wd.val)
    (himm : ∀ x ∈ exprFv c.term, ∀ pls k n, tbl.lookup x = some pls → pls[k]? = some (.imm n) →
      Λ.imms c.term x k = some n) :
    Placed Λ lbl s c := by
  refine ⟨fun x k => if x ∈ exprFv c.term then (tbl.lookup x).bind (·[k]?) else none, ?_, ?_, ?_⟩
  · intro x ty ws hl k wd wp hwd hwp
    dsimp only at hwp
    split at hwp
    · cases h : tbl.lookup x with
      | none => simp [h] at hwp
      | some pls => simp only [h, Option.bind_some] at hwp; exact hrep x pls ty ws h hl k wp wd hwp hwd
    · cases hwp
  · intro x hx ty ws hl k hk
    obtain ⟨pls, h, hle⟩ := htot x hx ty ws hl
    exact ⟨pls[k], by simp [hx, h, List.getElem?_eq_getElem (show k < pls.length by omega)]⟩
  · intro x k n hn
    dsimp only at hn
    split at hn
    · rename_i hx
      cases h : tbl.lookup x with
      | none => simp [h] at hn
      | some pls => simp only [h, Option.bind_some] at hn; exact himm x hx pls k n h hn
    · cases hn

/-! ## rodata's controls past the allocation -/

/-- **The layout's immediates at rodata's terms** past the allocation: `m`'s word `2` at the six terms up to
`let n`, the two lane constants at their exchanges, `sl`'s constant words `2`, `13` at `ret sl`. -/
structure RdImms (Λ : Scc.Sem.Layout) : Prop where
  m : ∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN], Λ.imms e "m" 0 = some 2
  w0 : Λ.imms eO0 "w0" 0 = some rdK1
  w1 : Λ.imms eO1 "w1" 0 = some rdK2
  sl1 : Λ.imms eRet "sl" 1 = some 2
  sl2 : Λ.imms eRet "sl" 2 = some 13

/-- **rodata's controls past the allocation** of the buffer at `l` (`ini` elements initialised), up to
`ret sl`, by term and environment (the hold is free). -/
def RdCH (l : WeakMem.AllocLabel) (ini : Nat) (c : Ctl) : Prop :=
  (c.term = eW0 ∧ c.env = envA l ini) ∨ (c.term = eO0 ∧ c.env = env1 l ini) ∨
  ∃ wo0, (c.term = eW1 ∧ c.env = env2 l ini wo0) ∨ (c.term = eO1 ∧ c.env = env3 l ini wo0) ∨
    ∃ wo1, (c.term = eS ∧ c.env = env4 l ini wo0 wo1) ∨ (c.term = eN ∧ c.env = env5 l ini wo0 wo1) ∨
      (c.term = eRet ∧ c.env = envR l ini wo0 wo1)

/-- The word of the buffer's base. -/
abbrev bw (l : WeakMem.AllocLabel) : Word := cst (.loc ⟨l, 0⟩ 0)

/-- The places of rodata's variables: the base at `pl`, the constants immediate. -/
def rdTbl (pl : Place M1.I.RegId) : Tbl :=
  [("b", [.one pl]), ("s", [.one pl]), ("m", [.imm 2]), ("w0", [.imm rdK1]), ("w1", [.imm rdK2]),
    ("sl", [.one pl, .imm 2, .imm 13])]

/-- **The words of rodata's variables** at its controls past the allocation. -/
theorem lookup_rd {l : WeakMem.AllocLabel} {ini : Nat} {c : Ctl} (hc : RdCH l ini c) {x : String} {ty : Ty}
    {ws : List Word} (hl : lookupE c.env x = some (ty, ws)) :
    (x = "b" → ws = [bw l]) ∧ (x = "s" → ws = [bw l]) ∧ (x = "m" → ws = [cst (.num 2)]) ∧
      (x = "w0" → ws = [cst (.num rdK1)]) ∧ (x = "w1" → ws = [cst (.num rdK2)]) ∧
      (x = "sl" → ws = [bw l, cst (.num 2), cst (.num 13)]) := by
  rcases hc with ⟨-, he⟩ | ⟨-, he⟩ | ⟨wo0, ⟨-, he⟩ | ⟨-, he⟩ | ⟨wo1, ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩⟩⟩ <;>
    rw [he] at hl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
    simp [lookupE, envR, env5, env4, env3, env2, env1, envA, bBind, envN,
      Spike.Lib.Hello1RodataSrc.env0] at hl <;> exact hl.2.symm

/-- rodata's terms past the allocation. -/
theorem term_rd {l : WeakMem.AllocLabel} {ini : Nat} {c : Ctl} (hc : RdCH l ini c) :
    c.term ∈ [eW0, eO0, eW1, eO1, eS, eN, eRet] := by
  rcases hc with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨wo0, ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨wo1, ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩⟩⟩ <;> simp [ht]

/-- The free variables of rodata's terms past the allocation. -/
theorem fv_rd : ∀ e ∈ [eW0, eO0, eW1, eO1, eS, eN, eRet], ∀ y ∈ exprFv e,
    y ∈ ["b", "s", "m", "w0", "w1", "sl"] := by
  decide

/-- **rodata's controls past the allocation are placed** at any place `pl` holding the buffer's base (`hpl`),
given the layout's immediates (`hI`). -/
theorem placed_rd (hI : RdImms Λ) {l : WeakMem.AllocLabel} {ini : Nat} {c : Ctl} (pl : Place M1.I.RegId)
    (hpl : ∃ v, placeVal M1 s pl = some v ∧ lbl l = some v) (hc : RdCH l ini c) : Placed Λ lbl s c := by
  refine placed_of_tbl (rdTbl pl) ?_ ?_ ?_
  · intro x hx ty ws hl
    have hw := lookup_rd hc hl
    have hfv : x ∈ ["b", "s", "m", "w0", "w1", "sl"] := fv_rd _ (term_rd hc) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, by simp [hw.1 rfl]⟩
    · exact ⟨_, rfl, by simp [hw.2.1 rfl]⟩
    · exact ⟨_, rfl, by simp [hw.2.2.1 rfl]⟩
    · exact ⟨_, rfl, by simp [hw.2.2.2.1 rfl]⟩
    · exact ⟨_, rfl, by simp [hw.2.2.2.2.1 rfl]⟩
    · exact ⟨_, rfl, by simp [hw.2.2.2.2.2 rfl]⟩
  · intro x pls ty ws hpls hl k wp wd hwp hwd
    have hw := lookup_rd hc hl
    by_cases e1 : x = "b"
    · subst e1; cases hpls; rw [hw.1 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hpl
      | _ + 1, hwp, _ => simp at hwp
    by_cases e2 : x = "s"
    · subst e2; cases hpls; rw [hw.2.1 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hpl
      | _ + 1, hwp, _ => simp at hwp
    by_cases e3 : x = "m"
    · subst e3; cases hpls; rw [hw.2.2.1 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
      | _ + 1, hwp, _ => simp at hwp
    by_cases e4 : x = "w0"
    · subst e4; cases hpls; rw [hw.2.2.2.1 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨rdK1_lt, rfl⟩
      | _ + 1, hwp, _ => simp at hwp
    by_cases e5 : x = "w1"
    · subst e5; cases hpls; rw [hw.2.2.2.2.1 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact ⟨rdK2_lt, rfl⟩
      | _ + 1, hwp, _ => simp at hwp
    by_cases e6 : x = "sl"
    · subst e6; cases hpls; rw [hw.2.2.2.2.2 rfl] at hwd
      match k, hwp, hwd with
      | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at hpl
      | 1, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
      | 2, hwp, hwd => cases hwp; cases hwd; exact ⟨by decide, rfl⟩
      | _ + 3, hwp, _ => simp at hwp
    · simp [rdTbl, List.lookup, beq_false_of_ne e1, beq_false_of_ne e2, beq_false_of_ne e3,
        beq_false_of_ne e4, beq_false_of_ne e5, beq_false_of_ne e6] at hpls
  · intro x hx pls k n hpls hn
    rcases hc with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨wo0, ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨wo1, ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩⟩⟩ <;>
      rw [ht] at hx ⊢ <;> revert hx <;> simp only [show exprFv eW0 = ["b", "b", "b", "m"] by decide,
        show exprFv eO0 = ["b", "w0", "b", "b", "m"] by decide, show exprFv eW1 = ["b", "b", "m"] by decide,
        show exprFv eO1 = ["b", "w1", "b", "m"] by decide, show exprFv eS = ["b", "m"] by decide,
        show exprFv eN = ["s", "m"] by decide, show exprFv eRet = ["sl"] by decide, List.mem_cons,
        List.not_mem_nil, or_false] <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> cases hpls <;>
      first
        | (match k, hn with | 0, hn => cases hn | _ + 1, hn => simp at hn)
        | (match k, hn with | 0, hn => cases hn; exact hI.m _ (by simp) | _ + 1, hn => simp at hn)
        | (match k, hn with
            | 0, hn => cases hn; first | exact hI.w0 | exact hI.w1
            | _ + 1, hn => simp at hn)
        | (match k, hn with
            | 0, hn => cases hn
            | 1, hn => cases hn; exact hI.sl1
            | 2, hn => cases hn; exact hI.sl2
            | _ + 3, hn => simp at hn)

/-! ## The setup call's frame -/

/-- **A slot of `scc_rt_main`'s frame across the call of `wc_rodata`**: past the callee's region (`R.callee
(-80) (-208) 8`, `Hello1.mR R`), a cell of the caller's frame `R` at `-72` or above is as at the call
(`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_keptR {R : Region} {o : SO} {m1 m' : MachineData} {σC : AS} (hA : Abs R o m1 σC)
    (hK : CKept R (-80) (-208) 8 m1 m') (hD : DFrame (R.callee (-80) (-208) 8) m' s.st.1) (hR : R.OK)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : -72 ≤ k) :
    placeVal M1 s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee (-80) (-208) 8).Off (k - -80) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have h80 := Region.addr_toNat_of hR (k := -80) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [privLoad, e, hK k hk hc, hj, hv]

/-- **The setup call's frame is placed** below `wc_rodata`'s call: `me`'s word `w` (`hme`) is the caller's
slot `km` at the call (`hlm`), at or above `-72` (`hkm`). -/
theorem framesPlaced_frH {env : Env} {w : Word} {R : Region} {m1 m' : MachineData} {σC : AS}
    {km : Int} (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hkm : R.Off km ∧ -72 ≤ km)
    (hme : ∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w]) (hlm : ValRep lbl w.val (σC.slot km).toNat)
    (hK : CKept R (-80) (-208) 8 m1 m') (hA : Abs R ⟨-80, []⟩ m1 σC)
    (hD : DFrame (mR R) m' s.st.1) : FramesPlaced Λ lbl s [frH env] :=
  Spike.Lib.X64SetupPlaced.framesPlaced_setupCont hme
    ⟨_, placeVal_slot_keptR hA hK hD hR hlo hhi hkm.1 hkm.2, hlm⟩

/-- The premises fixing the setup call's frame below `wc_rodata`'s call. -/
structure FrP (lbl : Lbl) (R : Region) (env : Env) (σC : AS) : Prop where
  ok : R.OK
  lo : R.lo ≤ -80
  hi : 0 ≤ R.hi
  km : ∃ km w, (R.Off km ∧ -72 ≤ km) ∧ (∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w]) ∧
    ValRep lbl w.val (σC.slot km).toNat

/-- **A control of rodata placed at the setup call's frame**. -/
theorem placedSE_rd {env : Env} {R : Region} {m1 m' : MachineData} {σC : AS}
    (hI : RdImms Λ) (hP : FrP lbl R env σC) {l : WeakMem.AllocLabel} {ini : Nat} {c : Ctl}
    (pl : Place M1.I.RegId) (hpl : ∃ v, placeVal M1 s pl = some v ∧ lbl l = some v) (hc : RdCH l ini c)
    (hK : CKept R (-80) (-208) 8 m1 m') (hA : Abs R ⟨-80, []⟩ m1 σC)
    (hD : DFrame (mR R) m' s.st.1) : PlacedSE Λ lbl s c [frH env] :=
  let ⟨_, _, hkm, hme, hlm⟩ := hP.km
  .inl (PlacedS.ofFrames (placed_rd hI pl hpl hc) (framesPlaced_frH hP.ok hP.lo hP.hi hkm hme hlm hK hA hD))

/-! ## The nodes -/

/-- The abstract run's simp set over concrete blocks (as in `X64WakeMainW`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-- **`rpB0`'s prefixes keep `%rax`** (the base: stored, then reloaded into `%rcx`). -/
theorem rpB0_rax (l : String → Int64) (pc : Int64) (o : SO) (σ : AS) {k : Nat} (hk : k < rpB0.length) :
    (arun l (rpB0.take k) ⟨pc, o, σ⟩).σ.regs.get64 .rax = σ.regs.get64 .rax := by
  simp only [rpB0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|k <;> (try omega) <;> arun_simp

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {m0 : MachineData}
  {σC : AS} {env : Env}

set_option hygiene false in
/-- The placement at the labels `lbl`, the setup call's frame. -/
local notation "PL" => fun s c => PlacedSE Λ lbl s c [frH env]

theorem off16 : (mR R).Off (-16) := by
  show (-16 : Int) % 8 = 0 ∧ (-208 : Int) ≤ -16 ∧ (-16 : Int) + 8 ≤ 8
  decide

/-- **A block keeping the base's slot `-16` is placed** once its invariant's controls are rodata's at a label
the labels put at that slot (`h`). -/
theorem blkW_plS (hI : RdImms Λ) (hP : FrP lbl R env σC) {n : ND} {blk : List (Directive × Nat)}
    (hk : keepsSlot (-16) n.o blk = true)
    (h : ∀ σ c, n.J σ c → ∃ l ini, lbl l = some (σ.slot (-16)).toNat ∧ RdCH l ini c) :
    BlkW (PL) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) n blk := by
  intro s σ c _ _ _ _ _ hF hJ k _ m hA' hD
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨l, ini, hl, hc⟩ := h σ c hJ
  refine placedSE_rd hI hP _ ⟨_, placeVal_cell hA' off16 _ rfl, ?_⟩ hc hF.2.1 hF.2.2 hD
  rw [arun_slot_keep _ (-16) blk ⟨n.pc, n.o, σ⟩ k hk]; exact hl

/-- **A node is placed** once its invariant's controls are rodata's at a label the labels put at the base's
slot `-16` (`h`). -/
theorem nodeW_plS (hI : RdImms Λ) (hP : FrP lbl R env σC) {n : ND}
    (h : ∀ σ c, n.J σ c → ∃ l ini, lbl l = some (σ.slot (-16)).toNat ∧ RdCH l ini c) :
    NodeW (PL) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) n := by
  rintro s c ⟨-, -, -, -, σ, hA, hF, hJ⟩
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨l, ini, hl, hc⟩ := h σ c hJ
  exact placedSE_rd hI hP _ ⟨_, placeVal_slot_abs hA off16, hl⟩ hc hF.2.1 hF.2.2 (DFrame.refl _ _)

/-- **`.x15`'s first block is placed**: the base is in `%rax` (`rpB0` writes only `%rcx` and the slot). -/
theorem blkW_plS0 (hI : RdImms Λ) (hP : FrP lbl R env σC) {n : ND}
    (h : ∀ σ c, n.J σ c → ∃ l ini, lbl l = some σ.regs.rax.toBitVec.toNat ∧ RdCH l ini c) :
    BlkW (PL) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) n rpB0 := by
  intro s σ c _ _ _ _ _ hF hJ k hk m hA' hD
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨l, ini, hl, hc⟩ := h σ c hJ
  refine placedSE_rd hI hP (.reg (.r .rax)) ⟨_, placeVal_reg _ .rax, ?_⟩ hc hF.2.1 hF.2.2 hD
  show lbl l = some (m.regs.get64 .rax).toNat
  rw [hA'.regs, rpB0_rax _ _ _ _ hk]; exact hl

end Nodes

/-! ## `wc_rodata` from the allocator's return -/

/-- `.x15`'s blocks past the first keep the base's slot `-16`. -/
theorem keeps16 : keepsSlot (-16) Spike.Lib.X64.Flow.Hello1.oR rpB1 = true ∧
    keepsSlot (-16) Spike.Lib.X64.Flow.Hello1.oR rpB2 = true ∧
    keepsSlot (-16) Spike.Lib.X64.Flow.Hello1.oR rpB3 = true ∧
    keepsSlot (-16) Spike.Lib.X64.Flow.Hello1.oR rpB4 = true := by
  decide +kernel

/-- **`wc_rodata` from the allocator's return inside the placement at the setup call's frame**
(`RdWfSF.rdPostW_WSHF`'s `hpl` at `[frH env]`, region `Hello1.mR R`, frame condition `Hello1.mF R F m0 σC`):
every control of the seven invariants is one of rodata's past the allocation at a label the labels put at
`.x15`'s `%rax` (`hC`), the layout's immediates are rodata's (`hI`), the frame's `me` is a caller's slot (`hP`). -/
theorem rdPostW_plS {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {m0 : MachineData} {σC : AS} {env : Env}
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} (hI : RdImms Λ) (hP : FrP lbl R env σC)
    (hC : ∀ σ0 c, (Jp σ0 c ∨ Jp' σ0 c ∨ J1 σ0 c ∨ J2 σ0 c ∨ J2' σ0 c ∨ J3 σ0 c ∨ J4 σ0 c) →
      ∃ l ini, lbl l = some σ0.regs.rax.toBitVec.toNat ∧ RdCH l ini c) :
    RdPostW (fun s c => PlacedSE Λ lbl s c [frH env]) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC)
      Jp Jp' J1 J2 J2' J3 J4 := by
  have fr : ∀ {σ0 σ : AS} {c : Ctl}, rdFr σ0 σ →
      (∃ l ini, lbl l = some σ0.regs.rax.toBitVec.toNat ∧ RdCH l ini c) →
      ∃ l ini, lbl l = some (σ.slot (-16)).toNat ∧ RdCH l ini c := fun hfr ⟨l, ini, hl, hc⟩ =>
    ⟨l, ini, by rw [hfr.1]; exact hl, hc⟩
  exact ⟨blkW_plS0 hI hP fun σ c h => hC σ c (.inl h),
    nodeW_plS hI hP fun _ c ⟨σ0, _, h, hfr, _⟩ => fr hfr (hC σ0 c (.inr (.inl h))),
    blkW_plS hI hP keeps16.1 fun _ c ⟨σ0, _, h, hfr⟩ => fr hfr (hC σ0 c (.inr (.inr (.inl h)))),
    nodeW_plS hI hP fun _ c ⟨σ0, _, h, hfr, _⟩ => fr hfr (hC σ0 c (.inr (.inr (.inl h)))),
    blkW_plS hI hP keeps16.2.1 fun _ c ⟨σ0, _, h, hfr⟩ => fr hfr (hC σ0 c (.inr (.inr (.inr (.inl h))))),
    nodeW_plS hI hP fun _ c ⟨σ0, _, h, hfr, _⟩ => fr hfr (hC σ0 c (.inr (.inr (.inr (.inr (.inl h)))))),
    blkW_plS hI hP keeps16.2.2.1 fun _ c ⟨σ0, _, h, hfr⟩ =>
      fr hfr (hC σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
    nodeW_plS hI hP fun _ c ⟨σ0, _, h, hfr, _⟩ => fr hfr (hC σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
    blkW_plS hI hP keeps16.2.2.2 fun _ c ⟨σ0, _, h, hfr⟩ =>
      fr hfr (hC σ0 c (.inr (.inr (.inr (.inr (.inr (.inr h)))))))⟩

end Spike.Lib.X64.HelloPh.RdPlS

/-- info: 'Spike.Lib.X64.HelloPh.RdPlS.placed_rd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdPlS.placed_rd

/-- info: 'Spike.Lib.X64.HelloPh.RdPlS.rdPostW_plS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdPlS.rdPostW_plS
