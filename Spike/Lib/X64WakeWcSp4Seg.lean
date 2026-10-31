/-
**wake.w's `wc_main` from `.x20` to its `clone`'s `syscall`** (x86-64, the
twin of `Spike/Lib/A64WakeWcSp4Seg.lean`), inside `W`, in any valid layout
of `wakeCells`: the blocks, nodes and edges of
`Spike/Lib/X64WakeWcSp4.lean` and `Spike/Lib/X64WakeClone.lean` composed
with the row and the call:

    .x20:     x20A                      (x20A_edge)
              movq %rax, 56(%rcx)       -- row: the TCB's tid word (rtst_ndW)
              initCall                  (initCall_edge)
    thread_init                         -- the callee (`hti`, the instance's)
    .x21:     … to the syscall          (WcClone.wake_wc_clone_segW)
    .x21+46:  syscall                   -- the exit `wcNS`

The second TCB `t` (`.x20`'s `%rax`), the reserve's id `1` at `-24`, the
cell `cA` and main's word `m` in the frame (`FrV`), the source at `c0`
throughout. `scc_rt_thread_init` returns the child's stack top `kOf lab`
(`tiBase + 16384` at the second take, `k0 = 16384`).

Where x86-64 differs from AArch64: the call pushes `.x21` at `-72`, so the
callee's region is `R.callee (-72) (-248) 8` (its entry offsets `⟨0, []⟩`,
its frame `[-248, 8)`); back from it only `%rsp`'s offset is known, so the
call lands at `n21I` (`%rbp` from the callee's postcondition, `wcNIR` the
call node with `%rbp` from its offsets) and `At.rbp` restores `oW`.

- `tidSt_eq`; `kOf`, `tiQ`: the stack top and the callee's ghosts;
- `XA`, `aN`: the nodes before the call (with `-24 = 1` up to the tid
  store); `wcNIR`, `n21I`: the call's nodes with `%rbp` in the invariant;
- `WcSp4PreW`, `WcSp4W`: the nodes' states inside `W` (up to the call; to
  the `syscall`);
- `wake_wc_sp4_pre_segW`, `wake_wc_sp4_ret_segW` (the call back to `.x21`,
  the callee promised `P` at its entry, `call_nd_FWP`),
  `wake_wc_sp4_call_segW`, `wake_wc_sp4_segW`: the segments.
-/
import Spike.Lib.X64WakeWcSp4
import Spike.Lib.X64WakeCloneIn
import Spike.Lib.X64Ret0
import Spike.Lib.X64CallP

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcSp4
open Spike.Lib.X64.WakePh.WcClone (oW x21L FrW wcN21 wcNS WcCloneW wake_wc_clone_segW)
open Spike.Lib.X64.Flow.Ret0 (TiG tiN tiX stacksA)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open SccCode (wakeCells)

set_option linter.unusedSimpArgs false

theorem tidSt_eq : tidSt = [(stDir .rcx 56 .rax, 4)] := by decide

/-- **The child's stack top** `scc_rt_thread_init` returns at the second
take: `tiBase` at `k0 = 16384`, plus `16384`. -/
abbrev kOf (lab : Label → Int64) : BitVec 64 := stacksA lab + 16384#64 + 16384#64

/-- The callee's ghosts: the frame's `g`, the TCB `t`, the second take's
`k0 = 16384`, the source control `c0`. -/
abbrev tiQ (t : BitVec 64) (c0 : Ctl) (g : Ret0.AllocTcb.G) : TiG := ⟨g, t, 16384#64, c0⟩

/-- `.x20`'s nodes before the call. -/
inductive XA where
  | n20 | n20s | n20p

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **The nodes before the call**: `WcSp4`'s, with the reserve's id `1` at
`-24` up to the tid store. -/
def aN : XA → ND
  | .n20 => ⟨lab x20L, oW, fun σ c => (wcN20 lab c0 t cA m fr).J σ c ∧ σ.slot (-24) = 1#64⟩
  | .n20s => ⟨lab x20L + 12, oW, fun σ c => (wcN20s lab c0 t cA m fr).J σ c ∧ σ.slot (-24) = 1#64⟩
  | .n20p => wcN20p lab c0 t cA m fr

/-- **The call node with `%rbp` from its offsets** (`At.rbp_get`): `%rbp`
`72` bytes above `%rsp`. -/
def wcNIR : ND := ⟨(wcNI lab c0 t cA m fr).pc, oC, fun σ c => (wcNI lab c0 t cA m fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -72)⟩

/-- **Back at `.x21`** with only `%rsp`'s offset known: `wcN21`'s facts at
the stack top `kOf lab`, `%rbp` `64` bytes above `%rsp` (`At.rbp` makes it
`wcN21`). -/
def n21I : ND := ⟨lab x21L, ⟨-64, []⟩, fun σ c => (wcN21 lab c0 t (kOf lab) cA m fr).J σ c ∧
  σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (0 - -64)⟩

end Nodes

/-- **`.x20`'s states up to the call inside `W`**, none moved by `K`: the
blocks' and the row's before the call, and the call node's (at `F`). -/
structure WcSp4PreW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n20 : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20) x20A
  n20s : NodeW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20s)
  n20p : BlkW W K exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20p) initCall
  nI : NodeW W K exe endPc R F (wcNI (_root_.Executable.labels exe).label c0 t cA m fr)

/-- Up to the call inside the trivial predicate, with no outside moves. -/
theorem WcSp4PreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcSp4PreW (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t cA m fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

/-- **`.x20`'s states to the `syscall` inside `W`**, none moved by `K`: the
blocks' and the row's before the call, the call node's (at `F`,
`WcSp4PreW`), and `.x21`'s to the `syscall` (at `F₂`, `WcCloneW`). -/
structure WcSp4W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) : Prop
    extends WcSp4PreW W K exe endPc R F c0 t cA m fr where
  clone : WcCloneW W K exe endPc R F₂ c0 t (kOf (_root_.Executable.labels exe).label) cA m fr

/-- From `.x20` to the `syscall` inside the trivial predicate, with no outside moves. -/
theorem WcSp4W.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcSp4W (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ c0 t cA m fr :=
  ⟨WcSp4PreW.triv, WcCloneW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x20` to the call of `scc_rt_thread_init`** (`wcNI`):
`wake_wc_sp4_segW`'s segment up to the call node, at the frame `F`; the
tid word `t + 56` a runtime word the store of `1` may write (`htid`). -/
theorem wake_wc_sp4_pre_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe wakeCells kp) (hend : endPc = endOf exe wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4PreW W K exe endPc R F c0 t cA m fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20))
      (At exe endPc R F (wcNI (_root_.Executable.labels exe).label c0 t cA m fr)) := by
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨b0, bs⟩, bp⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt wakeCells x20L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x20L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hA : SegW W K p lbl ms (At exe endPc R F (aN lab c0 t cA m fr .n20))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNI lab c0 t cA m fr) x) s c) := by
    refine fn_segW (N := aN lab c0 t cA m fr) (fun i => ?_) XA.n20
    cases i
    case n20 =>
      refine seg_ndW (by simp [x20A]) x20A_ok hF hR (by omega) hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x20L) x20A)) hW.n20
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XA.n20s, ?_⟩⟩
      have h := x20A_edge hJ.1
      refine ⟨h.1, h.2.1, h.2.2, ?_⟩
      show (arun lab x20A ⟨lab x20L, oW, σ⟩).σ.slot (-24) = 1#64
      have h24 : σ.slot (-24) = 1#64 := hJ.2
      rw [x20A_run]; simp [upd, h24]
    case n20s =>
      refine rtst_ndW (b := .rcx) (k := 56) (r := .rax) (z := 4)
        (fun s he hn => tidSt_eq ▸ code bs s he hn) hW.n20s fun m' σ c _ hD hJ => ?_
      obtain ⟨⟨h0, hcx, hax, h32, hFr⟩, h24⟩ := hJ
      have ha : bAddr σ.regs .rcx 56 = t + 56#64 := by rw [bAddr, hcx]; rfl
      have hv : σ.regs.get64 .rax = 1#64 := hax.trans h24
      obtain ⟨hrt, hmp, hG, hun⟩ := htid
      refine ⟨ha ▸ hrt, ha ▸ hmp, by rw [ha, hv]; exact hG, ha ▸ hun m' hD, c, .refl c,
        .inl ⟨XA.n20p, ?_, rfl, h0, h32, hFr⟩⟩
      show lab x20L + 16 = lab x20L + 12 + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    case n20p =>
      exact seg_ndW (by simp [initCall]) initCall_ok hF hR hlo hhi (fun s he hn => code bp s he hn) hW.n20p
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), initCall_edge hp hJ⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

/-- **The call of `scc_rt_thread_init`, back at `.x21`**: from the call node
(`wcNI`, the caller at `F ∧ P`) through the callee (`hti`, promised `P` at
its entry, `call_nd_FWP`) to `.x21` at the stack top `kOf lab` (`wcN21`,
`%rbp` from the callee's postcondition, `At.rbp`), the frame condition `F₂`.
The source control `c0` is any: the callee's ghost carries it through. -/
theorem wake_wc_sp4_ret_segW {W : Frag isa} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (wcNI (_root_.Executable.labels exe).label c0 t cA m fr))
      (At exe endPc R F₂ (wcN21 (_root_.Executable.labels exe).label c0 t
        (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  let lab := (_root_.Executable.labels exe).label
  refine ((Ret0.seg_oneW (n := n21I lab c0 t cA m fr)
    (call_nd_FWP (KC := True) (P := P) (e0 := 0) (lo' := -248) (hi' := 8) (M := M)
      (nC := wcNIR lab c0 t cA m fr)
      (Ne := fun g : Ret0.AllocTcb.G => tiN lab (tiQ t c0 g) .e)
      (Ex := fun g : Ret0.AllocTcb.G => tiX lab (tiQ t c0 g))
      hR hF (by show R.lo ≤ -72 - 0 + -248; omega) (by decide) (by show (-72 : Int) - 0 < R.hi; omega)
      (by show (-72 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-72 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
      (fun _ => hFK) (fun _ => hKR) hF₂
      (fun R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        hti R' F' hR' hlo' hhi' hF' (hK' trivial) hFF hR'e hcc g
          (let ⟨σC, c, h1, h2⟩ := hg; ⟨σC, c, h1.1, h2⟩)
          fun m' hm => let ⟨mC, σC, c, hA, hJ, hE, hk⟩ := hkeep m' hm; ⟨mC, σC, c, hA, hJ.1, hE, hk⟩)
      (fun _ => rfl) ?_ ?_)).mono_pre fun _ _ h => Ret0.At.rbp_get rfl h).mono_post
    fun _ _ h => Ret0.At.imp (At.rbp h fun _ _ h => h.2) fun _ _ h => h.1
  · rintro σC c ⟨⟨h0, hdi, -, -⟩, -⟩
    exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-72 - 0 + 0)⟩, rfl, h0, rfl, rfl, rfl, hdi⟩
  · rintro g ⟨⟩ σC c σx c' σR ⟨⟨-, -, h72, h16, h8, h32, hf1, hf2⟩, hb⟩ ⟨-, hsp, hfp, hra, -⟩
      ⟨hc', hsp', hfp', hrax⟩ hreg - - hsl
    have hkeep : ∀ k : Int, -64 ≤ k → k + 8 ≤ 16 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hsl k ⟨h3, by omega, by omega⟩ fun h => by simp only [Region.Off, Region.callee, wcNIR, oC] at h; omega
    refine .inl ⟨(), ?_, by show SO.le ⟨-64, []⟩ ⟨-72 - 0 + 8, []⟩ = true; decide, ⟨hc', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show lab x21L = Int64.ofBitVec g.ra
      rw [← hra]
      show _ = Int64.ofBitVec (σC.slot (-72 - 0 + 0))
      rw [show (-72 : Int) - 0 + 0 = -72 by decide, h72, int64_ofBitVec_toBitVec]
    · rw [hreg]; exact hrax
    · rw [hkeep (-16) (by omega) (by omega) (by omega), h16]
    · rw [hkeep (-8) (by omega) (by omega) (by omega), h8]
    · rw [hkeep (-32) (by omega) (by omega) (by omega), h32]
    · rw [hkeep 0 (by omega) (by omega) (by omega), hf1]
    · rw [hkeep 8 (by omega) (by omega) (by omega), hf2]
    · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (0 - -64)
      rw [hreg]
      simp only [Reg64s.get64] at hb ⊢
      rw [hfp', hsp', ← hfp, ← hsp]
      show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (0 - -64)
      rw [hb]; bv_omega

/-- **The call of `scc_rt_thread_init` to the `syscall`**: `wake_wc_sp4_segW`'s
segment from the call node, the callee promised `P` of the memory at its
entry (`call_nd_FWP`; the caller at `F ∧ P`). -/
theorem wake_wc_sp4_call_segW {W : Frag isa} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    {kp : Nat} (hp : Lays exe wakeCells kp) (hend : endPc = endOf exe wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4W W K exe endPc R F F₂ c0 t cA m fr)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (fun s c => At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (wcNI (_root_.Executable.labels exe).label c0 t cA m fr))
      (At exe endPc R F₂
        (wcNS (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  exact (wake_wc_sp4_ret_segW hF hR hlo hhi hF₂ hFK hKR hti).seq
    (wake_wc_clone_segW hp hend WakePh.wake_wcCloneIn hF₂s hR (by omega) hhi hW.clone)

/-- **`wc_main` from `.x20` to its `clone`'s `syscall` is one segment inside
`W`** in any valid layout of `wakeCells`: from `.x20` (the second TCB `t`
in `%rax`, the reserve's id `1` at `-24`, the frame's words `cA`, `m`, the
source at `c0`) to the `syscall` (`clone(855808, kOf lab, 0, 0, t)`). The
tid word `t + 56` is a runtime word the store of `1` may write (`htid`);
`scc_rt_thread_init` on `t` at the second take is the callee premise `hti`
(`call_nd_FW`'s, its frame `[-248, 8)` at `-72`, moving only memory `K`
keeps off the caller's cells: `hFK`, `hKR`), returning `kOf lab` with `M`
(the frame condition from `.x21` on is `F₂`, `hF₂`). Its states lie in `W`
(`hW`). -/
theorem wake_wc_sp4_segW {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe wakeCells kp) (hend : endPc = endOf exe wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcSp4W W K exe endPc R F F₂ c0 t cA m fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20))
      (At exe endPc R F₂
        (wcNS (_root_.Executable.labels exe).label c0 t (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  exact (wake_wc_sp4_pre_segW hp hend hF hR (by omega) hhi hW.toWcSp4PreW htid).seq
    ((wake_wc_sp4_call_segW (P := fun _ => True) hp hend hF hR hlo hhi hF₂s hF₂ hW hFK hKR
      fun R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        (hti R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep).mono_pre fun _ _ h => h.1).mono_pre
      fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, trivial⟩, hJ⟩)

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_pre_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_ret_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_ret_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_call_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_call_segW
