/-
**wake.w's `wc_main` from `.sp4` to its `clone`'s `svc`** (AArch64, the
pre-spawn consumer), inside `W`, in any valid layout of `wakeProg`: the blocks, nodes and edges (`Spike/Lib/A64WakeWcSp4.lean`) composed with the
two rows and the call:

    .sp4:     sp4A                      (sp4A_edge)
              str x9, [x10, #56]        -- row: the TCB's tid word (rtst_ndW)
              initCall                  (initCall_edge)
    thread_init                         -- the callee (`hti`, the instance's)
    .sp6:     sp6A                      (sp6A_edge)
              dmb ish                   -- row: a fence, the source stuttering (dmb_ndW)
              cloneArgs                 (cloneArgs_edge)
    .sp6+52:  svc #0                    -- the exit `wcNS`

The second TCB `t` (`.sp4`'s `x0`), the reserve's id `1` at `[sp, #16]`,
the cell `cA` and main's word `m` in the frame (`FrW`), the source at `c0`
throughout. `scc_rt_thread_init` returns the child's stack top `kOf lab`
(`tiBase + 16384` at the second take, `k0 = 16384`).

- `kOf`, `tiQ`: the stack top and the callee's ghosts;
- `aN`, `bN`: the nodes (with `[sp, #16] = 1` up to the tid store,
  and after the call at `kOf`); `wcNS` the exit at the `svc`;
- `WcSp4W`: the nodes' states inside `W`;
- `wake_wc_sp4_segW`: the segment, the callee given as a premise in
  `call_nd_FWK`'s form (`hti`, its frame of 256), the tid word's store a
  runtime store (`htid`).
-/
import Spike.Lib.A64WakeWcRes
import Spike.Lib.A64WakeWcSp4

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4
open Spike.Lib.A64.WakePh.Tcb2Call (oW)
open Spike.Lib.A64.Flow.Ret0 (TiG tiN tiX stacksA)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

set_option linter.unusedSimpArgs false

theorem tidSt_eq : tidSt = [strDir .X9 .X10 56] := by decide

theorem fenceB_eq : fenceB = [.instr ⟨.W64, .DMB .sy⟩] := by decide

/-- **The child's stack top** `scc_rt_thread_init` returns at the second
take: `tiBase` at `k0 = 16384`, plus `16384`. -/
abbrev kOf (lab : Label → Int64) : BitVec 64 := stacksA lab + 16384#64 + 16384#64

/-- The callee's ghosts: the frame's `g`, the TCB `t`, the second take's
`k0 = 16384`, the source control `c0`. -/
abbrev tiQ (t : BitVec 64) (c0 : Ctl) (g : Ret0.ThreadInit.G) : TiG := ⟨g, t, 16384#64, c0⟩

/-- `.sp4`'s nodes before the call. -/
inductive XA where
  | n4 | n4s | n5

/-- `.sp6`'s nodes after the call. -/
inductive XB where
  | n6 | n6f | n6a

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **The nodes before the call**, with the reserve's id `1` at
`[sp, #16]` up to the tid store. -/
def aN : XA → ND
  | .n4 => let n := wcN4F lab c0 t cA m fr; ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.slot (-64) = 1#64⟩
  | .n4s => let n := wcN4s lab c0 t cA m fr; ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.slot (-64) = 1#64⟩
  | .n5 => wcN5 lab c0 t cA m fr

/-- **The nodes after the call**, at the stack top `kOf lab`. -/
def bN : XB → ND
  | .n6 => wcN6 lab c0 t (kOf lab) cA m fr
  | .n6f => wcN6f lab c0 t (kOf lab) cA m fr
  | .n6a => wcN6a lab c0 t (kOf lab) cA m fr

end Nodes

/-- **`.sp4`'s states to the `svc` inside `W`**, none moved by `K`: the
blocks' and the rows'. -/
structure WcSp4W (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n4 : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n4) sp4A
  n4s : NodeW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n4s)
  n5 : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n5) initCall
  nI : NodeW W K exe endPc R F (wcNI (_root_.Executable.labels exe).label c0 t cA m fr)
  n6 : BlkW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 t cA m fr .n6) sp6A
  n6f : NodeW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 t cA m fr .n6f)
  n6a : BlkW W K exe endPc R F₂ (bN (_root_.Executable.labels exe).label c0 t cA m fr .n6a) cloneArgs

/-- From `.sp4` to the `svc` inside the trivial predicate, with no outside moves. -/
theorem WcSp4W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcSp4W (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ c0 t cA m fr :=
  ⟨BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv, fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv,
    fun _ _ _ => ⟨trivial, fun _ h => h⟩, BlkW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- A block's edge (`WcSp4.Edge`) is a hit at the target node. -/
theorem hit_of_edge {lab : Label → Int64} {blk : List Directive} {n n' : ND} {σ : AS} {c : Ctl}
    (h : Edge lab blk n n' σ c) (ho : n'.o = oW) : Hit n' (arun lab blk ⟨n.pc, oW, σ⟩) c :=
  ⟨h.1.symm, by rw [h.2.1, ho]; rfl, h.2.2⟩

/-- **`wc_main` from `.sp4` to the call of `scc_rt_thread_init`** (`wcNI`):
`wake_wc_sp4_segW`'s segment up to the call node, at the frame `F`. -/
theorem wake_wc_sp4_pre_segW {W : Frag isaLSE2} {K : State → State → Prop} {F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4W W K exe endPc R F F₂ c0 t cA m fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n4))
      (At exe endPc R F (wcNI (_root_.Executable.labels exe).label c0 t cA m fr)) := by
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b4, b4s⟩, b5⟩, -⟩, -⟩, -⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  -- before the call
  have hA : SegW W K p lbl ms (At exe endPc R F (aN lab c0 t cA m fr .n4))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNI lab c0 t cA m fr) x) s c) := by
    refine fn_segW (N := aN lab c0 t cA m fr) (fun i => ?_) XA.n4
    cases i
    case n4 =>
      refine seg_ndW (by simp [sp4A]) sp4A_ok hF hR hal (by omega) hhi (code_of hp hend b4 (ofNat4_zero _)) hW.n4
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XA.n4s, ?_⟩⟩
      have h := hit_of_edge (sp4A_edge hJ.1) rfl
      refine ⟨h.1, h.2.1, h.2.2, ?_⟩
      show (arun lab sp4A ⟨(wcN4F lab c0 t cA m fr).pc, oW, σ⟩).σ.slot (-64) = 1#64
      have h64 : σ.slot (-64) = 1#64 := hJ.2
      rw [sp4A_run]; simp [Spike.Lib.upd, h64]
    case n4s =>
      refine rtst_ndW (t := .X9) (b := .X10) (i := 56) (code_of hp hend (tidSt_eq ▸ b4s) rfl) hW.n4s
        fun m' σ c _ hD hJ => ?_
      obtain ⟨⟨h0, h9, h10, h56, hFr⟩, h64⟩ := hJ
      have ha : rAddr σ.regs .X10 56 = t + 56#64 := by rw [Ret0.rAddr_x10 h10]; rfl
      have hv : σ.regs.getRegOrZr (.low (.reg .X9) .W64) = 1#64 := by rw [Ret0.getRegOrZr_x9, h9, h64]
      obtain ⟨hrt, hmp, hG, hun⟩ := htid
      refine ⟨ha ▸ hrt, ha ▸ hmp, by rw [ha, hv]; exact hG, ha ▸ hun m' hD, c, .refl c,
        .inl ⟨XA.n5, ?_, rfl, h0, h56, hFr⟩⟩
      show lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4) = lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 3) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n5 =>
      refine seg_ndW (by simp [initCall]) initCall_ok hF hR hal (by omega) hhi (code_of hp hend b5 rfl) hW.n5
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), hit_of_edge (initCall_edge hp hJ) rfl⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

/-- **The call of `scc_rt_thread_init` to the `svc`**: `wake_wc_sp4_segW`'s
segment from the call node, the callee promised `P` of the memory at its
entry (`call_nd_FWP`; the caller at `F ∧ P`). -/
theorem wake_wc_sp4_call_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4W W K exe endPc R F F₂ c0 t cA m fr)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-256) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (wcNI (_root_.Executable.labels exe).label c0 t cA m fr))
      (At exe endPc R F₂
        (wcNS (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, b6⟩, b6f⟩, b6a⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  -- the call
  have hC : SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (wcNI lab c0 t cA m fr))
      (fun s c => ∃ x : Unit, At exe endPc R F₂ ((fun _ => bN lab c0 t cA m fr .n6) x) s c) := by
    refine (call_nd_FWP (KC := True) (P := P) (lo' := -256) (hi' := 0) (M := M) (nC := wcNI lab c0 t cA m fr)
      (N := fun x : Empty => x.elim)
      (E := fun _ : Unit => bN lab c0 t cA m fr .n6)
      (Ne := fun g : Ret0.ThreadInit.G => tiN lab (tiQ t c0 g) .e)
      (Ex := fun g : Ret0.ThreadInit.G => tiX lab (tiQ t c0 g))
      hR hal hF (by show R.lo ≤ -80 + -256; omega) (by decide) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 16 = 0; decide) (by decide) (by decide) (fun _ => hFK) (fun _ => hKR) hF₂
      (fun R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        hti R' F' hR' hal' hlo' hhi' hF' (hK' trivial) hFF hR'e hcc g hg hkeep)
      (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => ?_
    · rintro σC c ⟨h0, hx0, -, -, -⟩
      exact ⟨⟨σC.regs.SP.toBitVec, σC.regs.X29.toBitVec, σC.regs.X30.toBitVec⟩, rfl, h0, rfl, rfl, rfl, hx0⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨h0, -, h30, h56, h72, h80, h16, h8⟩ ⟨hc, -, -, h30', -⟩ ⟨hc', hpost⟩ hreg - hsl
      have hkeep : ∀ k : Int, -80 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wcNI]; omega)
      refine .inr ⟨(), ?_, rfl, hc'.trans hc.symm |>.trans h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show lab ".L21_wc_main.sp6" = Int64.ofBitVec g.ra
        rw [← h30']
        show _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, int64_ofBitVec_toBitVec]
      · rw [hreg, hpost.2.2.2]
      · rw [hkeep (-56) (by omega) (by omega) (by omega), h56]
      · rw [hkeep (-72) (by omega) (by omega) (by omega), h72]
      · rw [hkeep (-80) (by omega) (by omega) (by omega), h80]
      · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
      · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
    · rcases h with ⟨j, _⟩ | h
      · exact j.elim
      · exact h
  -- after the call
  have hB : SegW W K p lbl ms (At exe endPc R F₂ (bN lab c0 t cA m fr .n6))
      (fun s c => ∃ x : Unit, At exe endPc R F₂ ((fun _ => wcNS lab c0 t (kOf lab) cA m fr) x) s c) := by
    refine fn_segW (N := bN lab c0 t cA m fr) (fun i => ?_) XB.n6
    cases i
    case n6 =>
      refine seg_ndW (by simp [sp6A]) sp6A_ok hF₂s hR hal (by omega) hhi (code_of hp hend b6 (ofNat4_zero _))
        hW.n6 fun σ c hJ => ⟨c, .refl c, .inl ⟨XB.n6f, hit_of_edge (sp6A_edge hJ) rfl⟩⟩
    case n6f =>
      refine dmb_ndW (code_of hp hend (fenceB_eq ▸ b6f) rfl) hW.n6f fun σ c hJ =>
        ⟨c, .loc (.refl c), .inl ⟨XB.n6a, ?_, rfl, hJ⟩⟩
      show lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 4) = lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 3) + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n6a =>
      refine seg_ndW (by simp [cloneArgs]) cloneArgs_ok hF₂s hR hal (by omega) hhi (code_of hp hend b6a rfl)
        hW.n6a fun σ c hJ => ⟨c, .refl c, .inr ⟨(), hit_of_edge (cloneArgs_edge hJ) rfl⟩⟩
  exact (hC.seq (hB.mono_pre fun _ _ ⟨_, h⟩ => h)).mono_post fun _ _ ⟨_, h⟩ => h

/-- **`wc_main` from `.sp4` to its `clone`'s `svc` is one segment inside
`W`** in any valid layout of `wakeProg`: from `.sp4` (the second TCB `t` in
`x0`, the reserve's id `1` at `[sp, #16]`, the frame's words `cA`, `m`, the
source at `c0`) to the `svc` (`clone(855808, kOf lab, 0, t, 0)`). The tid
word `t + 56` is a runtime word the store of `1` may write (`htid`);
`scc_rt_thread_init` on `t` at the second take is the callee premise `hti`
(`call_nd_FWK`'s, its frame of 256, moving only memory `K` keeps off the
caller's cells: `hFK`, `hKR`), returning `kOf lab` with `M` (the frame
condition from `.sp6` on is `F₂`, `hF₂`). Its states lie in `W` (`hW`). -/
theorem wake_wc_sp4_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4W W K exe endPc R F F₂ c0 t cA m fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-256) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n4))
      (At exe endPc R F₂
        (wcNS (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  exact (wake_wc_sp4_pre_segW hp hend hF hR hal hlo hhi hW htid).seq
    ((wake_wc_sp4_call_segW (P := fun _ => True) hp hend hF hR hal hlo hhi hF₂s hF₂ hW hFK hKR
      fun R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        (hti R' F' hR' hal' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep).mono_pre fun _ _ h => h.1).mono_pre
      fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, trivial⟩, hJ⟩)

end Seg

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_segW

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_pre_segW

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_call_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_sp4_call_segW
