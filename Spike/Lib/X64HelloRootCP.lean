/-
**The child segment's premises at hello's root on x86-64** (the twin of `Spike/Lib/HelloRootCP.lean`):
`X64.Flow.Worker.Hello.SegR.ChildPrem` at the clone's data — the worker's self-word memory side
`X64HelloOwnLift.msWHX`, the child's first memory on the stub's region `childR stack (-272)`, main's
`%r12 %rbx %r13 %r14 %r15 %r9` (`X64HelloChildX.wordsX`), the thread pointer `%r8`, the handed stack's top — assembled
from the per-field producers at main's `clone` (`PreRH`, the pre-spawn relation) and at the pre-spawn fragment
(`X64HelloHPre.FrH`, the record's placement).

Per field: `hlimT`/`hlimW`/`hT` `X64HelloChildLimX` (the second TCB's words, `TcbArea` at the memory relation);
`hown` `X64HelloOwnLift.ownAt_msWHX` at `tls_tcbWH`; `hm` `X64HelloPreA.hm_clone`; `hx1`
`X64HelloChildX1.hx1_clone`; `hwm`/`hm0`/`hwn` the packet's words; `hsvc`
`X64HelloAssemblyI.hsvc_preRHX` (at `msWHX`); `hdm`
`X64HelloCellOff.hdm_preRH`; `hv`/`htag`/`hvu` `X64HelloSpawnR.words_clone`; `hv0`/`hv1`/`hv2`
`X64HelloCPWords.hv012_preRH`; `hS`/`htp4`/`hSx` `X64HelloChildStW.childPrem_St` lifted to `msWHX`
(`stOk_msXW`: both words off both self words); `habt` `X64HelloAssemblyI.habt_I` (`msXW` keeps `abortAt`).

From the fragment: at the clone the fragment is in level 3 (`X64HelloHClW.pc_of_cloneH`), its placement the
start's extended twice, so main's id label is at its TCB (`meW_H`: `%r9 = pinA + 8`, `CloneInvH`'s `%r9` clause),
and `%r8` is the second TCB (`X2H`'s clone clause).

- `stOk_msXW`: a runtime store's facts at `msXW`, the word off both self words.
- `r9_r8_ofR`: main's `%r9` and `%r8` at the clone from the fragment.
- `hCP_root`: the child premise with the `FrH Dd` antecedent. Open (layout facts): `hinit2` (the second limit
  word's initial value) and `hn3` (the pinned `.zero` reaching the second TCB's id word, `208` bytes).

## Differences from the AArch64 version

- The memory side is `msWHX` (owning the worker's TCB self word `pinA + 144`), not `msWH`: x86-64's `ChildPrem`
  has `hT` (the self word's load) and `hown` (its ownership), and its `hlimT`/`hlimW` are `LimOk`.
- The frame's depth is `-272`, as AArch64's (x86-64's `ChildD.ok` asks `lo ≤ -264`).
- The thread pointer is `%r8`, carried by the level-3 clone clause `X2H` (AArch64: `x3`, a premise `hx3`); main's
  id word is `%r9` (AArch64: `x14`).
- The cell's word is `%r15` (`wordsX`'s fifth), so `hv` is `words_clone`'s first part.
-/
import Spike.Lib.X64HelloChildLimX
import Spike.Lib.X64HelloChildStW
import Spike.Lib.X64HelloCellOff
import Spike.Lib.X64HelloCPSvc
import Spike.Lib.X64HelloCPSvcX
import Spike.Lib.X64HelloChildAbt
import Spike.Lib.X64HelloChildLim
import Spike.Lib.X64HelloChildRoot
import Spike.Lib.X64HelloBoxM
import Spike.Lib.X64HelloHClWR
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloHPre
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64HelloChildX1
import Spike.Lib.X64HelloCPWords
import Spike.Lib.X64HelloStackB

namespace Spike.Lib.X64HelloRootCP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Entry Range ValRep MemRelP)
open Scc.Sem.X64 (pcOf Asm)
open Scc.Sem.Kernel (callOf)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.Handover (childAfter handed)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (ChildPrem wordsX)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.Flow.HelloWc (tH)
open Spike.Lib.X64HelloPreA (clonePcH H0StmtH H1StmtHF)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.X64WakeW1 (mainTidW)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64HelloOwnLift (msWHX tcbWH)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH cwvH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64HelloH2Inv (inv2H cloneInv2_of x2H_of)
open Spike.Lib.X64HelloHClW (pc_of_cloneH)
open Spike.Lib.X64.PhRec (m0Of)
open Spike.Lib.X64HelloGOf2H (lim2AH)
open Spike.Lib.X64WakeOwnX (OffTcb msXW msXW_mp_of)

/-- **A runtime store's facts at `msXW`**, the word off both self words. -/
theorem stOk_msXW {ms : MemSide isa} {F : MachineData → Prop} {O T W a v : BitVec 64} (h : StOk ms F a v)
    (hT : OffTcb T ⟨a, 8⟩) (hW : OffTcb W ⟨a, 8⟩) : StOk (msXW ms O T W) F a v :=
  ⟨h.rt, msXW_mp_of h.mp hT hW, h.G, h.unmapped⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => LH hp i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

/-- **The two child stores' words are off both self words**: `pinA + 24` and `pinA + 168` miss `pinA + 8`'s and
`pinA + 144`'s words. -/
theorem offTcb_childSt {c : Nat} (hc : c = 24 ∨ c = 168) :
    OffTcb (Spike.Lib.X64.WakePh.tcbM (Ly)) ⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ ∧
      OffTcb (tcbWH (Ly)) ⟨(Ly).pinA + BitVec.ofNat 64 c, 8⟩ := by
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have hc' : c ≤ 168 := by omega
  have e : ∀ k, k ≤ 208 → ((Ly).pinA + BitVec.ofNat 64 k).toNat = (Ly).pinA.toNat + k := fun k hk => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  have e8 := e 8 (by decide)
  have e144 := e 144 (by decide)
  have ec := e c (by omega)
  show OffTcb ((Ly).pinA + BitVec.ofNat 64 8) _ ∧ OffTcb ((Ly).pinA + BitVec.ofNat 64 144) _
  simp only [OffTcb, ec, e8, e144]
  omega

section Frag

variable {μ : Marks} {Dd : ODataH} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa}
  {Start : FragS isa} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {a : Int64} {ls0 : Lsize}

/-- **main's `%r9` and `%r8` at the clone from the pre-spawn fragment** (module doc): at a `clone` call the
fragment is in the third level, at the start's placement extended twice; `CloneInvH` puts main's id label at
`%r9`, and that label is at main's TCB (`meW_H`); `%r8` is the second TCB by `X2H`'s clone clause. -/
theorem r9_r8_ofR (hN : NodesA (Ly).Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl)
    (hT : TakeSiteS helloSrc μ (IH Dd)) (hCl : ∀ s, Cl s → pcOf s = clonePcH (Ly))
    (h0 : H0StmtH W0 K Dd.L0 ms0 (Ly) Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 (Ly) Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 (Ly) a (Ly).endPc Dd.L0 ls0) (hL0 : Dd.L0 = LB)
    {lbl : Lbl} {lsize : Lsize} {th : Thread isa} {s : TermRun.Cfg} {stack tls : Nat}
    (hFr : Spike.Lib.X64HelloHPre.FrH Dd lbl lsize th s) (hsys : Scc.Sem.X64.abi.atSys th.st = true)
    (hcall : callOf Scc.Sem.X64.abi th = some (.clone stack tls)) :
    (th.st.st.1.regs.get64 .r9).toNat = ((Ly).pinA + 8#64).toNat ∧
      th.st.st.1.regs.get64 .r8 = tH (Ly).lab := by
  obtain ⟨th0, hd, -, hI⟩ := hFr
  have hpc := pc_of_cloneH hN hT hCl hI hsys hcall
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ |
    ⟨l1, b1, n1, l', b', n', hl1, -, hl', -, -, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  rw [hinv2] at hi
  refine ⟨?_, ((x2H_of hi).1 hpc).2.2.2.2.2.1⟩
  obtain ⟨-, -, -, -, -, -, -, hmt, -⟩ := cloneInv2_of hi hpc
  rw [hL0] at hl1 hl' hmt
  have hme := Spike.Lib.X64.HelloPh.ChildRoot.meW_H hp i
  have hne1 : mainTidLbl 2 ≠ l1 := fun h => by rw [← h, hme] at hl1; cases hl1
  have hne' : mainTidLbl 2 ≠ l' := fun h => by
    rw [← h] at hl'
    simp only [Spike.Lib.X64ConsumerA.upd, hne1, ite_false, hme] at hl'
    cases hl'
  simp only [Spike.Lib.X64ConsumerA.upd, hne1, hne', ite_false, hme, Option.some.injEq] at hmt
  exact hmt.symm

end Frag

section Root

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {cT : ιH hp i → Loc} {cS : ιH hp i → WeakMem.Address}
  {pT : ιH hp i → Loc} {Pa : ιH hp i → Spike.Lib.Inv2Core.Inv2Params isa} {passT : State → Prop}
  {M : Spike.Lib.X64WakeM0.MSide (ιH hp i)} {D : WSideH (ιH hp i)} {r0 r1 : ιH hp i → Range} {asm : Asm}
  {E : Entry} {μ : Marks} {Dd : ODataH} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa}
  {Start : FragS isa} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {a : Int64} {ls0 : Lsize}

/-- **The child premise at the root** (module doc), with the pre-spawn fragment's antecedent. -/
theorem hCP_root (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 208 ≤ nZ)
    /- layout fact (as wake's root): the second limit word starts at `0` -/
    (hinit2 : (m0Of (Ly).Λ o.prog o.secs).initVal ⟨lim2AH (Ly), 8⟩ = 0)
    (hR1 : ∀ d s, R1 d s → R1OH arch (Ly).Λ μ Dd XH d s)
    (hDcw : ∀ w, D.cw w = w.1.cwW) (hcS : ∀ w, cS w = w.1.cS) (hr1 : ∀ w, r1 w = r1Of (Ly).lab)
    (hL0 : Dd.L0 = LB)
    (hN : NodesA (Ly).Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH (Ly))
    (h0 : H0StmtH W0 K Dd.L0 ms0 (Ly) Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 (Ly) Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 (Ly) a (Ly).endPc Dd.L0 ls0) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 (ιH hp i) (SRH hp i) cT cS pT Pa (GH hp i (G0H hp i)) passT M D r0 r1) (Ly).Λ asm E 0
        d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 (SRH hp i) cT cS pT Pa (GH hp i (G0H hp i)) passT M D r0 r1 (Ly).Λ w d th stack s s' s0 s1 lbl
        lsize ts j own₀ l →
      Spike.Lib.X64HelloHPre.FrH Dd lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (Ly).exe (endH hp i) (Ly).pfx (SRH hp i w).lbl
          (fun _ => msWHX (Ly) (GH hp i (G0H hp i)) (SRH hp i) w)
          (DFrame (childR stack (-272)) (childAfter Scc.Sem.X64.abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
            th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP _ hR hFr T w0 w1 w2 w4 _ h4w h0w h1w h2w
  have ho : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  obtain ⟨h1R, -, -, hsys, -, -, h7, -⟩ := id hP
  have hV : Spike.Lib.X64HelloVBuf.VBufR s := (hR1 _ _ h1R).2.2.2.2.2
  have hth := hR.pre.threads
  obtain ⟨X, hC⟩ := hR.clone
  have hlb := Spike.Lib.X64HelloSpawnR.lbl_clone hR
  -- the clone call: the handed stack's top and `%r8`
  obtain ⟨th', -, -, tls', -, -, -, -, -, -, -, -, hth', -, -, -, -, hcall, -, h8, -⟩ := id hC
  obtain rfl : th = th' := by
    rw [hth] at hth'; exact List.singleton_inj.mp (congrArg Array.toList hth')
  have htop := hR.pre.top
  rw [htop] at hcall
  have etls : tls' = tls := (Scc.Sem.Kernel.Call.clone.inj (Option.some.inj (hcall.symm.trans h7))).2
  rw [etls] at h8
  -- the handed stack is the record's second take, in the pool
  have hsub1 : (r1Of (Ly).lab).Sub (Ly).Λ.stackPool := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13
  have hsub : (r1 w).Sub (Ly).Λ.stackPool := by rw [hr1]; exact hsub1
  obtain ⟨htop', -, hsz'⟩ := Spike.Lib.X64.HelloPh.StackB.childB_r1Of (Ly) hsub1
  rw [← hr1 w] at htop' hsz'
  have hszw : (r1 w).size = 16384 := by rw [hr1]; rfl
  have hh0 : handed d.2 0 ((r1 w).lo + (r1 w).size) = some (0, r1 w) := by simp [handed, hR.pre.held]
  -- the memory relation at the record's placement
  obtain ⟨hm, -⟩ := Spike.Lib.X64HelloCloneMem.memRelP_preRH hR
  -- the fragment: `%r9` main's TCB, `%r8` the second TCB
  obtain ⟨h9', hr8'⟩ := r9_r8_ofR hp i hN hT hCl h0 h1 hinv2 hL0 hFr hsys h7
  have htls : tls = (tH (Ly).lab).toNat := by rw [← h8, hr8']
  have hpin3 := Spike.Lib.X64HelloTcbArea.hpin3_H hp i hz hn3
  -- the record's pointer word
  have hcw : (D.cw w).val = .loc (cS w) 0 := by rw [hDcw, hcS]; exact cwvH hp i w
  obtain ⟨hv, -, hvu⟩ := Spike.Lib.X64HelloSpawnR.words_clone hR hcw
  have hv' := hv
  rw [hcw] at hv'
  -- the cell's placed address
  obtain ⟨-, x, hx, hx15⟩ := hv'
  rw [hR.hcS] at hx
  have hcA : lbl l = some x := by
    simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff, Nat.mul_zero, Nat.add_zero] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hb
  have e15 : th.st.st.1.regs.get64 .r15 = BitVec.ofNat 64 x := by
    have hlt := (th.st.st.1.regs.get64 .r15).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  -- `hlimT`/`hlimW`/`hT`/`hown`
  have hheld : d.2.held = [(0, r1Of (Ly).lab), (0, r0 w)] := by rw [← hr1 w]; exact hR.pre.held
  have htopR : (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size = stack := by rw [← hr1 w]; exact htop
  have hlo : -(-272 : Int) ≤ 16384 := by decide
  -- `hS`/`htp4`/`hSx`
  have hmeW : BitVec.ofNat 64 (th.st.st.1.regs.get64 .r9).toNat = (Ly).pinA + 8#64 := by
    rw [h9', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htlsB : BitVec.ofNat 64 tls = (Ly).pinA + 144#64 := Spike.Lib.X64HelloChildLimX.tls_tcbWH hp i htls
  obtain ⟨hS, htp4, hSx⟩ := Spike.Lib.X64HelloChildStW.childPrem_St hp i hm
    (Spike.Lib.X64.HelloPh.ChildRoot.hpin2_H hp i hz (by omega))
    (G := GH hp i (G0H hp i) w) (fun a ha => Spike.Lib.X64.HelloPh.ChildRoot.hG_childH' hp i w.1.cT ha)
    hmeW htlsB (x := d.2) (tid := 0) (th := th) (lo := -272) hh0 hsub (by omega)
    (AbW := Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels (Ly).exe).label)
  have e9 : BitVec.ofNat 64 (th.st.st.1.regs.get64 .r9).toNat = th.st.st.1.regs.get64 .r9 := by simp
  rw [e9] at hS htp4
  rw [htop] at hS hSx
  have e24 : th.st.st.1.regs.get64 .r9 + 16#64 = (Ly).pinA + BitVec.ofNat 64 24 := by
    rw [← e9, hmeW]; bv_omega
  have e168 : BitVec.ofNat 64 tls + 24#64 = (Ly).pinA + BitVec.ofNat 64 168 := by rw [htlsB]; bv_omega
  -- the slice words
  obtain ⟨hv0, hv1, hv2⟩ := Spike.Lib.X64HelloCPWords.hv012_preRH hV hR h0w h1w h2w
  exact {
    hlimT := Spike.Lib.X64HelloChildLimX.limT_cloneHX hp i hpin3 hinit2 hsub1 w hm hheld htopR htls hlo
    hT := Spike.Lib.X64HelloChildLimX.ldT_cloneHX hp i hpin3 hsub1 w hm hheld htopR htls hlo
    hown := by rw [htlsB]; exact Spike.Lib.X64HelloOwnLift.ownAt_msWHX
    hlimW := fun rbp ra σ c hJ hsp =>
      Spike.Lib.X64HelloChildLimX.limW_cloneHX hp i hpin3 hinit2 hsub1 w hm hheld htopR htls hlo rbp ra σ c hJ hsp
    hm := Spike.Lib.X64HelloPreA.hm_clone hC hth
    hx1 := fun rbp ra sp σ fl hJ => Spike.Lib.X64HelloChildX1.hx1_clone hC hth _ _ _ rbp ra sp σ fl hJ
    hwm := h1w
    hm0 := by decide
    hwn := h2w
    hsvc := Spike.Lib.X64HelloAssemblyI.hsvc_preRHX hp i ho (G0H hp i) hV hR h0w h2w
    hdm := by
      show ∀ m : MachineData, _ → Mem.loadInt m.dmem (th.st.st.1.regs.get64 .r15) 8 = none
      rw [e15, ← htop]
      exact Spike.Lib.X64HelloCellOff.hdm_preRH hR (Spike.Lib.X64HelloCloneMem.wf_LH hp i) hsub hh0 htop' (by omega) hcA
    hv := by rw [hlb, ← hDcw]; exact hv
    htag := ⟨w.1.cS, cwvH hp i w⟩
    hvu := hlb ▸ hvu w4 h4w
    hv0 := hv0
    hv1 := hv1
    hv2 := hv2
    hS := by
      rw [e24] at hS ⊢
      exact stOk_msXW hS (offTcb_childSt hp i (.inl rfl)).1 (offTcb_childSt hp i (.inl rfl)).2
    htp4 := htp4
    hSx := by
      rw [e168] at hSx ⊢
      exact stOk_msXW hSx (offTcb_childSt hp i (.inr rfl)).1 (offTcb_childSt hp i (.inr rfl)).2
    habt := Spike.Lib.X64HelloAssemblyI.habt_I hp i (G0H hp i) w }

end Root

end Spike.Lib.X64HelloRootCP

/-- info: 'Spike.Lib.X64HelloRootCP.stOk_msXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootCP.stOk_msXW

/-- info: 'Spike.Lib.X64HelloRootCP.offTcb_childSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootCP.offTcb_childSt

/-- info: 'Spike.Lib.X64HelloRootCP.r9_r8_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootCP.r9_r8_ofR

/-- info: 'Spike.Lib.X64HelloRootCP.hCP_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloRootCP.hCP_root
