import WeakCore.TermSpawnFinal
/-!
# TermSpawnMain — the spawn lemma, proved (statement: the frozen TermSpawnStmt minus `hbuf`:
WitBuf is dead, so no buffer-walk hypothesis)

`machine_tokens_spawnF` follows separately (needs `ObligationsF.bufScope`).
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The spawn lemma** (internal; hypotheses may change). -/
theorem startOK_spawnS {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 th : TTh} {f : String} {ts : List Ty} {d : Decl} {a : At} {rt : Ty} {res : List Word}
    {kids : List Kid}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre) (h1 : cpre.ths.size = 1)
    (hpre : cpre.ths[0]? = some th0) (hset : th0.term = .tail f [] (.var "a") ts) (hstk0 : th0.stack = []) (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) (hnp : AllNoProm cs)
    (hth : cs.ths[0]? = some th) (hret : th.term = .ret a) (hstk : th.stack = []) (hev : evalAt th.env a = some (rt, res))
    (hkids : kids ≠ []) (hok : ∀ kd ∈ kids, KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) :
    StartOK p k arch Init (fun _ => True) (spawnS cs res kids) :=
  startOK_spawnS_proved O0 hk h0 h1 hpre hset hstk0 hd hR0 hR0a hR0w hrun hnp hth hret hstk hev hkids hok

end TermSpawn

#print axioms TermSpawn.startOK_spawnS
