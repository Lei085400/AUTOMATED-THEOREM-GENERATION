import json
import re

def read_symbols_json(
        file_name: str
        ) -> list[str]:
        """读比赛给的symbols.json文件, 返回 $v 类型的变量 list"""
        
        # 读取JSON文件
        with open(file_name, 'r', encoding='utf-8') as file:
            data = file.readlines()

        # 解析JSON数据并存储为Python对象的列表
        known_symbols = [json.loads(line.strip()) for line in data]
        v_defs = []
        for symbol in known_symbols:
            conclusion = symbol['conclusion'].split()
            v_def = conclusion[1]
            if v_def not in v_defs:
                v_defs.append(v_def)
        # print(v_defs)
        return v_defs


def transform_json_to_mm(
          json_filepath : str,
          mm_filepath :str,
          def_cs = '',
          def_vs = '',
          ) -> None:
        """将固定格式的.json文件转换为metamath格式，
        追加到给定.mm文件"""

        with open(json_filepath, 'r', encoding='utf-8') as file:
            data = file.readlines()
        # 解析JSON数据并存储为Python对象的列表
        theorems = [json.loads(line.strip()) for line in data]

        mm_file = open(mm_filepath, "a")
        if def_cs:
            mm_file.write('$c ' + def_cs + ' $.' + '\n') ## $c 
        if def_vs:
            mm_file.write('$v ' + def_vs + ' $.' + '\n') ## $c 
        
        for theorem in theorems:
            label = theorem['theorem']
            type = theorem['type']
            conclusion = theorem['conclusion']
            e_hyps = theorem['e_hypos']
            f_hyps =  theorem['f_hypos']
            # dvs = theorem['d_vars']
            proof_steps = theorem['proof_steps']
            # references = theorem['references']
            #向mm文件写入
            if type == '$p':
                if e_hyps:
                    for i, eh in enumerate(e_hyps):
                        mm_file.write(f"{label}.{i+1} $e {eh} $.\n")
                mm_file.write(f"{label} {type} {conclusion} $= {proof_steps} $.\n")
            else:
                mm_file.write(label +' '+ type +' '+ conclusion +' '+ '$.' + '\n')
        mm_file.close()

def extract_string(input_string):
    # 定义正则表达式模式
    pattern = r'(wff|setvar|class)\s+(\w+)'

    # 使用正则表达式进行匹配
    match = re.search(pattern, input_string)

    # 如果匹配成功，返回提取的字符串，否则返回None
    if match:
        return match.group(2).strip()
    else:
        return None
 

def read_axioms_json_append(
        file_name : str,    #文件路径
        def_cs :list,
        def_vs:list
        ) : #-> tuple[list[Assertion],list[str]]:
        """读比赛给的axioms.json文件, 返回转换得到的assersion数组"""
        
        # 读取JSON文件
        with open(file_name, 'r', encoding='utf-8') as file:
            data = file.readlines()
        # 解析JSON数据并存储为Python对象的列表
        known_axioms = [json.loads(line.strip()) for line in data]
        for axiom in known_axioms:
            conclusion = axiom['conclusion'].split(' ')
            # print(conclusion)
            for item in conclusion:
                if item not in def_cs and item not in def_vs:
                    def_cs.append(item)
                    print('dcs_append new:',item)    
        # def_cs = " ".join(def_cs)       
        return def_cs

def read_symbols_json_append(
        file_name: str,
        def_cs: list
        ) :
        # 读取JSON文件
        with open(file_name, 'r', encoding='utf-8') as file:
            data = file.readlines()
        # 解析JSON数据并存储为Python对象的列表
        known_symbols = [json.loads(line.strip()) for line in data]
        
        for symbol in known_symbols:
            conclusion = symbol['conclusion'].split()
            c_append = conclusion[0]
            if c_append not in def_cs:
                def_cs.append(c_append)
        # print(v_defs)
        # def_cs = " ".join(def_cs)      
        return def_cs


def anatomy(axiom_file,symbol_file):
    def_vs = ' '.join(read_symbols_json(symbol_file)) 
    def_cs = """( ) -> -. wff |- & => <-> /\ \/ , if- -/\ \/_ -\/ A. setvar class = T. F. hadd cadd E. F/ [ / ] e. E* E! { | } F/_ =/= e/ _V CondEq [. ]. [_ ]_ \ u. i^i C_ C. /_ \
                (/) if ~P <. >. U. |^| U_ |^|_ Disj_ |-> Tr _I _E Po Or Fr Se We X. `' dom ran |` " o. Rel Pred Ord On Lim suc iota : Fun Fn --> -1-1-> -onto-> -1-1-onto-> ` Isom iota_ oF oR [C.] _om 1st 2nd supp \
                tpos curry uncurry Undef wrecs Smo recs rec seqom 1o 2o 3o 4o +o .o ^o Er /. ^m ^pm X_ ~~ ~<_ ~< Fin finSupp fi sup inf OrdIso har ~<_* CNF TC R1 rank |_| inl inr card aleph cf AC_ CHOICE Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 GCH InaccW Inacc WUni wUniCl Tarski \
                Univ tarskiMap N. +N .N <N +pQ .pQ <pQ ~Q Q. 1Q /Q +Q .Q *Q <Q P. 1P +P. .P. <P ~R R. 0R 1R -1R +R .R <R <RR CC RR 0 1 _i + x. <_ +oo -oo RR* < - -u NN 2 3 4 5 \
                6 7 8 9 NN0 NN0* ZZ ; ZZ>= QQ RR+ -e +e *e (,) (,] [,) [,] ... ..^ |_ |^ mod == seq ^ ! _C # Word lastS ++ <" "> substr prefix splice reverse repeatS cyclShift cyclShiftOLD t+ t* ^r t*rec shift sgn Re Im * sqrt \
                abs +- limsup ~~> ~~>r O(1) <_O(1) sum_ prod_ FallFac RiseFac BernPoly exp _e sin cos tan _pi _tau || bits sadd smul gcd lcm _lcm Prime numer denom odZ phi pCnt Z[i] AP MonoAP PolyAP Ramsey #p Struct ndx sSet Slot Base |`s +g .r *r Scalar .s .i TopSet le \
                oc dist UnifSet Hom comp |`t TopOpen topGen Xt_ 0g gsum Xs_ ^s ordTop RR*s "s /s qTop Xs. Moore mrCls mrInd ACS Cat Id Homf comf oppCat Mono Epi Sect Inv Iso ~=c C_cat |`cat Subcat Func idFunc o.func |`f Full Faith Nat FuncCat InitO TermO ZeroO domA codA Arrow HomA IdA compA \
                SetCat CatCat ExtStrCat Xc. 1stF 2ndF pairF evalF curryF uncurryF DiagFunc HomF Yon Proset Dirset Poset lt lub glb join meet Toset 1. 0. Lat CLat ODual toInc DLat PosetRel TosetRel DirRel tail +f Mgm Smgrp Mnd MndHom SubMnd freeMnd varFMnd EndoFMnd Grp invg -g .g ~QG SubGrp NrmSGrp GrpHom GrpIso \
                ~=g GrpAct Cntr Cntz oppG SymGrp pmTrsp pmSgn pmEven od gEx pGrp pSyl LSSum proj1 ~FG freeGrp varFGrp CMnd Abel CycGrp DProd dProj SimpGrp mulGrp 1r SRing Ring CRing oppR ||r Unit Irred invr /r RPrime RingHom RingIso ~=r DivRing Field SubRing RingSpan SubDRing AbsVal *Ring *rf LMod .sf LSubSp LSpan \
                LMHom LMIso ~=m LBasis LVec subringAlg ringLMod RSpan LIdeal 2Ideal LPIdeal LPIR NzRing RLReg Domn IDomn PID UFD AssAlg AlgSpan algSc mPwSer mVar mPoly <bag ordPwSer evalSub eval selectVars mHomP mPSDer AlgInd PwSer1 var1 Poly1 coe1 toPoly1 evalSub1 eval1 PsMet *Met Met ball fBas filGen MetOpen metUnif CCfld ZZring ZRHom ZMod
                chr Z/nZ RRfld PreHil .if ocv ClSubSp toHL proj Hil OBasis (+)m freeLMod unitVec LIndF LIndS maMul Mat DMat ScMat maVecMul matRRep matRepV subMat maDet maAdju minMatR1 ConstPolyMat matToPolyMat cPolyMatToMat decompPMat pMatToMatPoly CharPlyMat Top TopOn TopSp TopBases int cls Clsd nei limPt Perf Cn CnP ~~>t Kol2 Fre Haus Reg Nrm CNrm PNrm \
                Comp Conn 1stc 2ndc Locally N-Locally Ref PtFin LocFin kGen tX ^ko KQ Homeo ~= Fil UFil UFL FilMap fLimf fLim fClus fClusf CnExt TopMnd TopGrp tsums TopRing TopDRing TopMod TopVec UnifOn unifTop UnifSt UnifSp toUnifSp uCn CauFilU CUnifSp *MetSp MetSp toMetSp norm NrmGrp toNrmGrp NrmRing NrmMod NrmVec normOp NGHom \
                NMHom II -cn-> Htpy PHtpy ~=ph *p Om1 OmN pi1 piN CMod CVec CPreHil toCPreHil CauFil Cau CMet CMetSp Ban CHil RR^ EEhil vol* vol MblFn L^1 S.1 S.2 S. S_ _d 0p limCC _D Dn C^n mDeg deg1 Monic1p Unic1p quot1p rem1p idlGen1p Poly Xp coeff deg quot AA Tayl \
                Ana ~~>u log ^c logb arcsin arccos arctan area gamma zeta _G log_G 1/_G theta Lam psi ppi mmu sigma DChr /L TarskiG Itv LineG TarskiGC TarskiGB TarskiGCB TarskiGE TarskiGDim>= cgrG Ismt leG hlG pInvG raG perpG hpG midG lInvG cgrA inA leA eqltrG toTG EE Btwn Cgr EEG .ef Vtx iEdg Edg UHGraph USHGraph UPGraph UMGraph USPGraph USGraph SubGraph FinUSGraph NeighbVtx \
                UnivVtx ComplGraph ComplUSGraph VtxDeg RegGraph RegUSGraph EdgWalks Walks WalksOn Trails TrailsOn Paths SPaths PathsOn SPathsOn ClWalks Circuits Cycles WWalks WWalksN WWalksNOn WSPathsN WSPathsNOn ClWWalks ClWWalksN ClWWalksNOn ConnGraph EulerPaths FriendGraph Plig GrpOp GId inv /g AbelOp CVecOLD NrmCVec +v BaseSet .sOLD 0vec -v normCV IndMet .iOLD SubSp LnOp normOpOLD BLnOp 0op \
                adj HmOp CPreHilOLD CBan CHilOLD ~H +h .h 0h -h .ih normh Cauchy ~~>v SH CH _|_ +H span vH \/H 0H C_H projh 0hop Iop +op .op -op +fn .fn normop ContOp LinOp BndLinOp UniOp HrmOp normfn null ContFn LinFn adjh bra ketbra <_op eigvec eigval Lambda States CHStates \
                HAtoms <oH MH MH* class-n class-o _ . /e oMnd oGrp toCyc sgns <<< Archi SLMod oRing oField |`v PrmIdeal MaxIdeal IDLsrg Spec dim /FldExt /FinExt /AlgExt [:] subMat1 litMat CovHasRef Ldlf Paracomp ~Met pstoMet HCmp QQHom RRHom RRExt RR*Hom ManTop _Ind sum* oFC sigAlgebra sigaGen BrSiga sX measures Ddelta ae ~ae MblFnM toOMeas \
                toCaraSiga sitg sitm itgm seqstr Fibci Prob cprob rRndVar oRVC repr vts TarskiG2D AFS leftpad _pred _Se _FrSe _trCl _TrFo AcyclicGraph Retr PConn SConn CovMap e.g |g A.g Fmla Sat SatE |= =g /\g -.g ->g <->g \/g E.g AxExt AxRep AxPow AxUn AxReg AxInf ZF mCN mVR mType mTC \
                mAx mVT mREx mEx mDV mVars mRSubst mSubst mVH mPreSt mStRed mStat mFS mCls mPPSt mThm m0St mSA mWGFS mSyn mESyn mGFS mTree mST mSAX mUFS mUV mVL mVSubst mFresh mFRel mEval mMdl mUSyn mGMdl mItp mFromItp IntgRing cplMetSp HomLimB HomLim polyFld splitFld1 splitFld polySplitLim ZRing GF GF_oo ~Qp /Qp \
                Qp Zp _Qp Cp TrPred wsuc WLim frecs No <s bday <_s <<s |s _M _Old _N _L _R (x) Bigcup SSet Trans Limits Fix Funs Singleton Singletons Image Cart Img Domain Range pprod Apply Cup Cap Succ Funpart FullFun Restrict UB LB << >> XX. OuterFiveSeg TransportTo InnerFiveSeg Cgr3 Colinear FiveSeg Seg<_ OutsideOf Line LinesEE Ray _/_\ _/_\^n Hf Fne gcdOLD Prv E** F// sngl tag Proj (| ,, |) pr1 pr2 elwise Moore_ -Set-> -Top-> -Mgm-> -TopMgm-> curry_ uncurry_ [s ]s RR>=0 RR>0 _Id ~P_* ~P^* {R inftyexpitau \
                CCinftyN 1/2 inftyexpi CCinfty CCbar pinfty minfty RRbar infty CChat RRhat +cc -cc <rr Arg .cc invc iomnn NNbar ZZbar ZZhat ||C FinSum RRVec End ^^ wl-in TotBnd Bnd Ismty Rn Ass ExId Magma SemiGrp MndOp GrpOpHom RingOps DivRingOps RngHom RngIso ~=R Com2 Fld CRingOps Idl PrIdl MaxIdl PrRing Dmn \
                IdlGen |X. ,~ ~ Rels _S Refs RefRels RefRel CnvRefs CnvRefRels CnvRefRel Syms SymRels SymRel Trs TrRels TrRel EqvRels EqvRel CoElEqvRels CoElEqvRel Redunds Redund redund DomainQss DomainQs Ers ErALTV MembErs MembEr Funss FunsALTV FunALTV Disjss Disjs Disj ElDisjs ElDisj Prt LSAtoms LSHyp <oL LFnl LKer LDual OP cm OL OML \
                <o Atoms AtLat AtsLat CvLat HL LLines LPlanes LVols Lines Points PSubSp pmap +P PCl _|_P PSubCl LHyp LAut WAtoms PAut LDil LTrn Dil Trn trL TGrp TEndo EDRing EDRingR DVecA DIsoA DVecH ocA vA DIsoB DIsoC DIsoH ocH joinH LPol LCDual mapd HVMap HDMap1 HDMap HGMap HLHil -R PrjSp \
                PrjSpn NoeACS mzPolyCld mzPoly Dioph Pell1QR Pell14QR Pell1234QR PellFund []NN rmX rmY LFinGen LNoeM LNoeR ldgIdlSeq Monic Poly< degAA minPolyAA _ZZ IntgOver MEndo CytP TopSep TopLnd r* hereditary Scott Coll _Cc +r -r .v PtDf RR3  line3 (. ). ->. ->.. ,. liminf ~~>* SAlg SalOn SalGen sum^ Meas OutMeas CaraGen voln* voln SMblFn iota' defAt ''' (( )) '''' e// RePart <> Pairs \
                PrPairs FermatNo Even Odd FPPr GoldbachEven GoldbachOddW GoldbachOdd GrIsom IsomGr UPWalks MgmHom SubMgm clLaw assLaw comLaw intOp clIntOp assIntOp MgmALT CMgmALT SGrpALT CSGrpALT Rng RngHomo RngIsom RngCat RngCatALTV RingCat RingCatALTV DMatALT ScMatALT linC LinCo linIndS linDepS /_f _O #b digit LineM Sphere setrecs Pg >_ > sinh cosh tanh sec csc cot log_ Reflexive Irreflexive A! 1-1 """
    
    def_cs = def_cs.split()
    
    def_cs = read_axioms_json_append(axiom_file, def_cs, def_vs)
    def_cs = read_symbols_json_append(symbol_file,def_cs)
    def_cs = " ".join(def_cs)   
    mm_filepath = 'Declare.mm'
    mm_file = open(mm_filepath, "a")
    transform_json_to_mm(symbol_file,mm_filepath,def_cs,def_vs)
    transform_json_to_mm(axiom_file,mm_filepath)
    mm_file.write("wnew $p  $=  $.")
    mm_file.close()


# if __name__ == "__main__":
#     axioms_filepath = 'axioms.json' # 给定公理集
#     symbols_filepath = 'symbols.json' # 给定符号集
#     anatomy(axioms_filepath,symbols_filepath)
