(* ::Package:: *)

(***** General linear algebra functions ******)


(*Canonical basis vector of \[DoubleStruckCapitalR]^n: Subscript[(Subscript[e, i]), j]=Subscript[\[Delta], ij]*)
e[i_,n_]:=SparseArray[{{i}->1,{n}->0}]//Normal;


(* ::Input::Initialization:: *)
(***** General su(N) functions *****)


(* ::Input::Initialization:: *)
(*Commutator*)
Comm[x_,y_]:=x . y-y . x


(* ::Input::Initialization:: *)
(*Compute a totally antisymmetric rank-3 tensor efficiently*)
(*The independent elements are computed only once*)
AntiSym3Tensor[ElementFunc_,n_]:=(indices=Flatten[Table[{i,j,k},{i,1,n},{j,i+1,n},{k,j+1,n}],2];
tensor=ConstantArray[0,{n,n,n}];(*Do[tensor[[ind[[1]],ind[[2]],ind[[3]]]]=ElementFunc@@Flatten[{ind,Sqrt[n+1]}],{ind, indices}]; *)
Do[tensor[[ind[[1]],ind[[2]],ind[[3]]]]=ElementFunc@@ind,{ind, indices}];
6*Symmetrize[tensor,Antisymmetric[{1,2,3}]]//Normal)


(* ::Input::Initialization:: *)
(*Reshape a totally antisymmetric 3 tensor into a N^2xN^2xN^2 matrix*)
Reshape3tensor[T_]:=(d=Length[T];pairs=Flatten[Table[{i,j},{i,Range[d]},{j,Range[d]}],1];ind=(Table[If[p[[1]]<p[[2]],FirstPosition[pairs,p][[1]]],{p,pairs}]/.Null->Sequence[]);ArrayReshape[T,{d^2,d}][[ind]])


(* ::Input::Initialization:: *)
(*Custodially ordered generalized Gell-Mann matrices*)
GellMann[n_]:=GellMann[n]=
Flatten[Table[(*Antisymmetric case*)SparseArray[{{j,k}->-I,{k,j}->+I},{n,n}],{j,1,n-1},{k,j+1,n}],1]~Join~Flatten[Table[(*Symmetric case*)SparseArray[{{j,k}->1,{k,j}->1},{n,n}],{j,1,n-1},{k,j+1,n}],1]~Join~Table[(*Diagonal case*)Sqrt[2/l/(l+1)] SparseArray[Table[{j,j}->1,{j,1,l}]~Join~{{l+1,l+1}->-l},{n,n}],{l,1,n-1}]


(* ::Input::Initialization:: *)
GellMannVec[N_]:=Normal[GellMann[N]]


(* ::Input::Initialization:: *)
\[Lambda][i_,N_]:=GellMannVec[N][[i]]


(* ::Input::Initialization:: *)
(*Two functions for the structure constants:*)


(* ::Input::Initialization:: *)
f[N_]:=AntiSym3Tensor[f2[#1,#2,#3,N]&,N^2-1]//Simplify;


(* ::Input::Initialization:: *)
f2[i_,j_,k_,N_]:=-I/4 Tr[(\[Lambda][i,N] . \[Lambda][j,N]-\[Lambda][j,N] . \[Lambda][i,N]) . \[Lambda][k,N]];


(* ::Input::Initialization:: *)
(*Adjoint matrix associated to U\[Element]SU(N)*)


(* ::Input::Initialization:: *)
(*SU(N) Group adjoint*)
Adj[U_]:=(n=Dimensions[U][[1]];Table[1/2 Tr[ConjugateTranspose[U] . \[Lambda][i,n] . U . \[Lambda][j,n]],{i,1,n^2-1},{j,1,n^2-1}])


(*su(N) Lie algebra adjoint*)
adj[X_]:=(d=Dimensions[X][[1]];x=Table[1/2 Tr[X . \[Lambda][i,d]],{i,1,d^2-1}];Sum[-2*I*x[[i]]*f[d][[i,;;,;;]],{i,1,d^2-1}])


(* ::Input::Initialization:: *)
(*su(N) matrix associated to a vector v\[Element]R^(N^2-1)*)
Mat[v_]:=(dim=Sqrt[Dimensions[v][[1]]+1];If[dim\[Element]Integers ,Sum[v[[i]]*\[Lambda][i,dim],{i,1,dim^2-1}],Print["Bad vector dimension. Expected a vector of \!\(\*SuperscriptBox[TemplateBox[{},\n\"Reals\"], \(\*SuperscriptBox[\(N\), \(2\)] - 1\)]\)"]])


(* ::Input::Initialization:: *)
(*Random SU(N) matrix*)
RandomUnitary[N_]:=RandomVariate[CircularUnitaryMatrixDistribution[N]]
(*Perform a random change of basis for an adjoint matrix*)
ChangeBasis[matrix_]:=(dim=Sqrt[Dimensions[matrix][[1]]+1];If[dim\[Element]Integers,R=Adj[RandomUnitary[dim],dim];R . matrix . Transpose[R]//Chop,Print["Bad matrix dimension. Expected a \!\(\*SuperscriptBox[\(N\), \(2\)]\)-1 square matrix"]])


(*Random su(N) element*)
Randomsu[N_]:=Sum[RandomReal[{0,4*Pi}]*\[Lambda][i,N],{i,1,N^2-1}]


(* ::Input::Initialization:: *)
(*F-product*)
Fprod[a_,b_]:=(dim=Length[a];If[Sqrt[dim+1]\[Element]Integers,f[Sqrt[dim+1]] . b . a//Chop,Print["Bad vector dimension. Expected two vectors of \!\(\*SuperscriptBox[TemplateBox[{},\n\"Reals\"], \(\*SuperscriptBox[\(N\), \(2\)] - 1\)]\)"]])


(************************* Lie algebra functions *************************)


BasisFromIndices[Evecs_,idx_]:=(basis=(Mat/@(Evecs[[idx]])//Chop);
g=Table[1/2 Tr[basis[[i]] . basis[[j]]],{i,1,Length[idx]},{j,1,Length[idx]}]//Chop;
If[Max[(IdentityMatrix[Length[idx]]-g)//Chop]!=0,Print["Warning! Possibly non-orthonormal basis!"];
Print[g]];
Return[basis])


(* Calculate the adjoint representation of the basis elements of an algebra *)
(* N.B.! This assumes the basis is orthonormal w.r.t the inner product 1/2Tr(*.*) *)
AdjointRep[basis_]:=(d=Length[basis];Table[I/2 Tr[Comm[basis[[i]],basis[[j]]] . basis[[k]]],{i,1,d},{j,1,d},{k,1,d}]//Chop)


(*Simultaneous diagonalization of a set of commuting matrices*)
SimulDiag[matrixList_]:=Sum[RandomReal[{-1,1}]*M,{M,matrixList}]//Eigenvectors


(* Calculate the rank of an algebra as the dimension of the nullspace of a regular element in the adjoint rep*)
CalcRank[basis_]:=(d=Dimensions[basis][[2]]; 
AdjBasis=AdjointRep[basis];
d - MatrixRank[Sum[RandomReal[]*AdjBasis[[i]],{i,1,Length[basis]}]])


(*Components of a Cartan subalgebra in that basis*)
CartanSubalg[basis_]:=(AdjBasis=AdjointRep[basis]; Sum[RandomReal[]*X,{X,AdjBasis}]//NullSpace//Chop)


(*Go to a Cartan-Weyl basis*)
CartanWeyl[basis_]:=(AdjBasis=AdjointRep[basis];
RandAdj=Sum[RandomReal[]*X,{X,AdjBasis}];
h=RandAdj//NullSpace//Chop;
r=Length[h];
ea=Eigensystem[RandAdj][[2]][[;;-r-1]]//Chop;
V=SimulDiag[Table[vec . basis,{vec,h}]]//Chop//Transpose;
H=Table[ConjugateTranspose[V] . (vec . basis) . V,{vec,h}];
Ea=Table[ConjugateTranspose[V] . (vec . basis) . V,{vec,ea}];
Return[{H,Ea}//Chop])


(*Calculate the root system of an algebra given a Cartan-Weyl basis for it*)
RootSys[H_,Ea_]:=Table[1/2 Tr[ConjugateTranspose[X] . Comm[h,X]],{X,Ea},{h,H}]//Chop


(*Find a set of positive simple root vectors within a root system*)
(*!! BUG: Sometimes returns more than r vectors !!*)
(* This bug inherited by all functions below *)
SimpleRootsVec[RootSystem_]:=(r=Dimensions[RootSystem][[2]];
n=RandomReal[{-1,1},r]//Normalize;Rplus=Select[RootSystem,# . n>0&];
Nvec=Length[Rplus];SimpleRoots={};
pairs=Flatten[Table[{i,j},{i,1,Nvec},{j,i+1,Nvec}],1];
Do[Decomp=False;For[k=1,k<=Nvec (Nvec-1)/2,k++,If[x==Chop[Rplus[[pairs[[k]][[1]]]]+Rplus[[pairs[[k]][[2]]]]],Decomp=True]];
If[Not[Decomp],AppendTo[SimpleRoots,x]],{x,Rplus}];
SimpleRoots)


(*Returns a set of positive simple roots for an algebra given a basis*)
GetSimpleRoots[basis_]:=({H,Ea}=CartanWeyl[basis];Rts=RootSys[H,Ea];SRts=SimpleRootsVec[Rts];
idx=Position[Rts,#]&/@SRts//Flatten;Return[Ea[[idx]]])


(*Returns Dynkin labels of a representation given a basis*)
DynkinLabels[basis_]:=(Ep=GetSimpleRoots[basis];
HW=Flatten[Select[Eigensystem[Sum[RandomReal[{-1,1}]*X,{X,Ep}]]//Chop//Transpose,(#[[1]]==0 && FreeQ[#[[2]],{0..}])&][[;;,2;;]],1];
Table[v0=Chop[ConjugateTranspose[X] . vec];
If[!FreeQ[v0,{0..}],0,a=0;
While[FreeQ[v0,{0..}],a++;
v0=Chop[ConjugateTranspose[X] . v0]];a],{vec,HW},{X,Ep}])


(************************* Inputting and manipulating potentials *************************)


(*Product of doublets*)
B[i_,j_]:=Conjugate[\[Phi][i]] . \[Phi][j]


(*Construct the potential from the cartesian tensor couplings Z and Y*)
TensorPot[Z_,Y_]:=(n=Length[Y];
Quiet[TensorContract[TensorProduct[Z,Table[Conjugate[\[Phi][a]] . \[Phi][b]Conjugate[\[Phi][c]] . \[Phi][d],{a,1,n},{b,1,n},{c,1,n},{d,1,n}]],{{1,5},{2,6},{3,7},{4,8}}]+TensorContract[TensorProduct[Y,Table[Conjugate[\[Phi][a]] . \[Phi][b],{a,1,n},{b,1,n}]],{{1,3},{2,4}}]]//Chop)


(*Nicely display the doublets in an expression*)
PrettyPrint[expr_]:=(n=Sqrt[Length[Variables[expr]]];subs=Table[Conjugate[\[Phi][i]] . \[Phi][j]->Subscript[SuperDagger[\[Phi]], i] . Subscript[\[Phi], j],{i,1,n},{j,1,n}]//Flatten;(expr//FullSimplify)/.subs)


(*Find the bilinear couplings of a given potential by rewriting all products Subscript[\[Phi]^\[Dagger], a].Subscript[\[Phi], b] in terms of bilinears Subscript[r, i]*)
(*The terms of the potential have to be written as e.g. Conjugate[\[Phi][i]].\[Phi][j]Conjugate[\[Phi][k]].\[Phi][l]*)
BilinearCouplings[pot_,n_]:=(X=Table[\[Lambda][i,n]//Flatten,{i,1,n^2-1}];
X=AppendTo[X,Table[If[Mod[i,n+1]==1,1,0],{i,1,n^2}]]//Inverse;
products=X . Table[K[i],{i,Mod[Range[n^2],n^2]}];
pairs=Flatten[Table[{i,j},{i,1,n},{j,1,n}],1];
subs=Table[Conjugate[\[Phi][pairs[[i]][[1]]]] . \[Phi][pairs[[i]][[2]]]->products[[i]],{i,1,n^2}];
(P=pot/.subs;
\[CapitalLambda]=Table[If[i==j,Coefficient[P,K[i]K[j]],1/2 Coefficient[P,K[i]K[j]]],{i,1,n^2-1},{j,1,n^2-1}]);
L=Table[Coefficient[P,K[0]K[i]],{i,1,n^2-1}];
M=Table[Coefficient[P,K[i]],{i,1,n^2-1}]/.Table[K[i]->0,{i,0,n^2-1}];
\[CapitalLambda]0=Coefficient[P,K[0]K[0]];
M0=Coefficient[P,K[0]]/.Table[K[i]->0,{i,0,n^2-1}];
Return[{\[CapitalLambda],L,M,\[CapitalLambda]0,M0}])


(*Construct the potential from the bilinear couplins \[CapitalLambda],Subscript[L, 0],Subscript[M, 0]*)
BilinearPot[\[CapitalLambda]_,L_,M_,\[CapitalLambda]0_,M0_]:=(n=Sqrt[Length[M]+1];
r=Table[Sum[\[Lambda][i,n][[a,b]]*Conjugate[\[Phi][a]] . \[Phi][b],{a,n},{b,n}],{i,1,n^2-1}];
r0=Sum[Conjugate[\[Phi][a]] . \[Phi][a],{a,1,n}];
pot=r . \[CapitalLambda] . r+M . r+r0*L . r+\[CapitalLambda]0*r0^2+M0*r0)


(*Transformation of a set of bilinear couplings (\[CapitalLambda],L,M,Subscript[L, 0],Subscript[M, 0]) under a change of basis U*)
TransformedBilinearCouplings[bilinearC_,U_]:=(R=Adj[U];
Return[{R . bilinearC[[1]] . Transpose[R]//Simplify,R . bilinearC[[2]]//Simplify,R . bilinearC[[3]]//Simplify,bilinearC[[4]],bilinearC[[5]]}])


(*************************** CS *************************** )


(* ::Input::Initialization:: *)
(***** Functions for computing the manifestly custodial invariant block *****)


(* ::Input::Initialization:: *)
(*This function returns the index of the (CS-ordered) Gell-Mann matrix which has -i at position (a,b)*)
(*i.e. f(1,2)=1, f(1,3)=2,...,f(N-1,N)=1/2N*(N-1)*)


(* ::Input::Initialization:: *)
index[a_,b_,N_]:=Position[Flatten[Table[{i,j},{i,1,N-1},{j,i+1,N}],1],{a,b}][[1,1]]


(* ::Input::Initialization:: *)
(*Then we have Im(Subscript[\[Phi]^\[Dagger], a]Subscript[\[Phi], b]) = 1/2Subscript[\[Phi]^\[Dagger], i]Subscript[(Subscript[\[Lambda], f(a,b)]), ij]Subscript[\[Phi], j] where the function f is defined above*)


(* ::Input::Initialization:: *)
(*To generate a term Im(Subscript[\[Phi]^\[Dagger], a]Subscript[\[Phi], b])Im(Subscript[\[Phi]^\[Dagger], c]Subscript[\[Phi], d]), \[CapitalLambda] must have a 1/2 at positions (f(a,b),f(c,d)) and (f(c,d),f(a,b))*)
(*Thus we can construct Subscript[I^(4), abcd] *)


(* ::Input::Initialization:: *)
CSinv[a_,b_,c_,d_,N_]:=(L=SparseArray[{{index[a,b,N],index[c,d,N]}->1,{index[a,d,N],index[b,c,N]}->1,{index[a,c,N],index[b,d,N]}->-1},{1/2 N(N-1),1/2 N(N-1)}];1/2 (L+Transpose[L])//Normal)


(* ::Input::Initialization:: *)
(*To get the most general CS invariant block we sum over all distinct permutations of abcd weighted by independent coeffecients Subscript[\[Lambda], abcd]*)


(* ::Input::Initialization:: *)
CSblock[N_]:=Sum[\[Lambda][a,b,c,d]*CSinv[a,b,c,d,N],{a,1,N-3},{b,a+1,N-2},{c,b+1,N-1},{d,c+1,N}]


(* ::Input::Initialization:: *)
(*Returns a full custodial symmetric \[CapitalLambda] matrix*)
(*randomCouplings: if set to True, then the couplings Subscript[\[Lambda], abcd] are given random numerical values*)
(*randomLowerBlock: if set to True, then the lower 1/2N(N+1)x1/2N(N+1) block is a random symmetric matrix. Otherwise it's the identity*)


(* ::Input::Initialization:: *)
(*Generate a manifestly custodial symmetric \[CapitalLambda] matrix*)
\[CapitalLambda][N_,randomCouplings_,randomLowerBlock_]:=(If[randomLowerBlock, lowerBlock=RandomReal[{-4Pi,4Pi},{1/2 N(N+1)-1,1/2 N(N+1)-1}1];lowerBlock=1/2 (lowerBlock+Transpose[lowerBlock]),lowerBlock=IdentityMatrix[1/2 N(N+1)-1]];
CSb=CSblock[N];
L=ArrayFlatten[{{CSb,ConstantArray[0,{1/2 N(N-1),1/2 N(N+1)-1}]},{ConstantArray[0,{1/2 N(N+1)-1,1/2 N(N-1)}],lowerBlock}}];
If[randomCouplings,L/.Table[Variables[CSb][[i]]->RandomReal[{-4Pi,4Pi}],{i,1,Binomial[N,4]}],L])


(*Perform a random rotation on the lower block \[CapitalLambda]*)
(*Random O(N) matrix*)
RandomOrth[n_]:=RandomVariate[CircularRealMatrixDistribution[n]];
(*Function to embed a smaller matrix in the lower rightmost block of a larger matrix*)(*with 1's on the diagonal of the upper left block*)
embedMatrixWithDiagonal[smallMatrix_,{rows_,cols_}]:=Module[{smallRows,smallCols,rowOffset,colOffset,largeMatrix},(*Dimensions of the smaller matrix*){smallRows,smallCols}=Dimensions[smallMatrix];
(*Calculate the offsets to position the small matrix at the lower rightmost block*)rowOffset=rows-smallRows+1;
colOffset=cols-smallCols+1;
(*Create a larger matrix filled with zeros*)largeMatrix=ConstantArray[0,{rows,cols}];
(*Fill the diagonal of the upper left block with 1's*)Do[If[i<=Min[rows,cols],largeMatrix[[i,i]]=1],{i,Min[rows,cols]}];
(*Embed the smaller matrix into the larger matrix*)Do[largeMatrix[[i+rowOffset-1,j+colOffset-1]]=smallMatrix[[i,j]],{i,smallRows},{j,smallCols}];
largeMatrix]
(*Random O(N) matrix similarity transformation of lower, no-custodial block:*)
LowBlockObfuscAux[matrix_]:=(dim=Dimensions[matrix][[1]]; n=Sqrt[dim+1];k=n (n-1)/2;
orth=RandomOrth[dim-k];
embedMatrixWithDiagonal[orth,Dimensions[matrix]])
(*Function that obfuscates the lower N^2-1-k x N^2-1-k block by
an orthogonal similarity transformation of that block:*)
LowBlockObfusc[matrix_]:=(obfusc=LowBlockObfuscAux[matrix]; obfusc . matrix . Transpose[obfusc]);


(***** 4HDM specific functions *****)


(* ::Input::Initialization:: *)
(*A Function that returns the indices of the 2 sets of 3-fold degenerate eigenvectors
It takes a list of eigenvalues as argument*)


(* ::Input::Initialization:: *)
idx[evals_]:=(Ev=ReverseSortBy[Tally @ Round[evals,0.000001],Last][[2,1]];
Join[Position[Round[evals,0.000001],Ev],Position[Round[evals,0.000001],-Ev]]//Flatten)


(* ::Input::Initialization:: *)
(***** 4HDM specific functions *****)
(*A function that returns the 6 eigenvectors of the custodial block ordered as V^(\[PlusMinus]1), V^(\[PlusMinus]2), V^(\[PlusMinus]3), V^(\[MinusPlus]1), V^(\[MinusPlus]2), V^(\[MinusPlus]3)*)
Subspace4[matrix_]:=(eig=Eigensystem[matrix];
id = idx[eig[[1]]];
ev=eig[[2]][[id,;;]])//Chop


(* ::Input::Initialization:: *)
(***** 5HDM specific functions *****)
(*A function that returns the 10 eigenvectors of the custodial block*)
(*ordered as V^(01), V^(02), V^(03), V^(04), V^(\[PlusMinus]1), V^(\[PlusMinus]2), V^(\[PlusMinus]3), V^(\[MinusPlus]1), V^(\[MinusPlus]2), V^(\[MinusPlus]3)*)


(* ::Input::Initialization:: *)
Subspace5[matrix_]:=(eig=Eigensystem[matrix];
id = idx[eig[[1]]];
ev=Table[If[i>4,eig[[2,id[[i-4]]]],eig[[2,20+i]]],{i,1,10}])//Chop


(*************************** CP *************************** )


(*Manifestly CP2 conserving \[CapitalLambda] matrix*)
(*N is the number of doublets*)
\[CapitalLambda]CP[N_]:=(k=(N*(N-1))/2;L0=ArrayFlatten[{{RandomReal[{-4Pi,4Pi},{k,k}],ConstantArray[0,{k,N^2-1-k}]},{ConstantArray[0,{N^2-1-k,k}],RandomReal[{-4Pi,4Pi},{N^2-1-k,N^2-1-k}]}}];
L0=1/2 (L0+Transpose[L0]);L0)


(*Given a basis for a subspace, return an orthonormal basis of the subspace orthogonal to L and M*)
LMorthogonalize[subspace_,L_,M_]:=(d=Length[subspace];
OrthoBasis=Normalize/@Select[subspace,Chop[# . L]==0 && Chop[# . M]==0&];
NonOrthoBasis=Normalize/@Select[subspace,Chop[# . L]!=0 || Chop[# . M]!=0&];
(*Partition the initial basis according to LM-orthogonality*)
q=Length[NonOrthoBasis];
If[d>1,
If[Length[NonOrthoBasis]>1,
l=Table[Chop[L . v],{v,NonOrthoBasis}];
m=Table[Chop[M . v],{v,NonOrthoBasis}];
eqs={l . Table[b[k],{k,Range[q]}]==0,m . Table[b[k],{k,Range[q]}]==0};
sols=Solve[eqs,Table[b[k],{k,Range[q]}]]//Quiet//Chop;
x=Table[b[k],{k,1,q}]/.sols[[1]]//Chop;
If[Length[sols[[1]]]==0||!FreeQ[x,{0..}],Return[OrthoBasis],
linearIndep=False;While[!linearIndep, subs=Table[var->RandomReal[{-1,1}],{k,1,Length[Variables[x]]},{var,Variables[x]}];
orthoVecs=Normalize/@Table[(x . NonOrthoBasis)/.sub,{sub,subs}];
linearIndep=(orthoVecs//Transpose//NullSpace//Length)==0];
Return[Orthogonalize[orthoVecs]]],Return[OrthoBasis]],OrthoBasis])


(*Return a maximal set of eigenvectors orthogonal to L and M*)
(*Applies LMorthogonalize to each eigenvalue subspace*)
LMbasis[Lambda_,L_,M_]:=({evals,evecs}=Eigensystem[Lambda]//N//Chop;
distinctEvals=DeleteDuplicates[evals, Abs[#1 - #2]<10^-12 &];
subspacesIdx=Table[Position[evals,x_/;x==lambda]//Flatten,{lambda,distinctEvals}];
subspaces=Table[evecs[[idx]],{idx,subspacesIdx}];Flatten[Table[LMorthogonalize[subspace,L,M],{subspace,subspaces}],1])


(* ::Input::Initialization:: *)
(* Z-matrix i.e. structure constants for a set of orthonormal vectors *)
Zmat[Evecs_,L_,M_]:=(d=Length[L];
struct=f[Sqrt[d+1]];elemFunc[i_,j_,k_]:=(struct . Evecs[[j]] . Evecs[[i]]) . Evecs[[k]];Reshape3tensor[AntiSym3Tensor[elemFunc,Length[Evecs]]]//Chop)


(* ::Input::Initialization:: *)
AllPairs[indices_]:=(d=Dimensions[indices][[1]];Flatten[Table[{indices[[i]],indices[[j]]},{i,1,d},{j,i+1,d}],1])


SubsetAnyQ[set_,subsets_]:=(bool=False;Do[bool=bool||SubsetQ[set,s];If[bool,Break[]],{s,subsets}];Return[bool])
SubsetsExcluding[M_,k_,excluded_]:=(S={};Do[S=Union[S,Sort[Flatten[Prepend[#,tuple]]]&/@Subsets[DeleteElements[M,tuple],{k-Length[tuple]}]],{tuple,excluded}];S=Complement[Subsets[M,{k}],S])


(* Search for a subalgebra in a set of LM-orthogonal eigenvectors *)
(*The fourth argument LastStep is a boolean deciding whether or not the last step, which can be 
computationally expensive should be performed*)
SubalgebraSmartSearch[Lambda_,L_,M_,LastStep_]:=(n=Sqrt[Length[L]+1];k=(n(n-1))/2;If[EvenQ[n],R=n/2,R=(n-1)/2];
Evecs=LMbasis[Lambda,L,M];
Print[Length[Evecs]," eigenvectors are LM-orthogonal!"];
If[Length[Evecs]<k,Print["No LM-orthogonal ",k, "-d subalgebra!"];Return[{}]];
Z=Zmat[Evecs,L,M];
q=Dimensions[Z][[2]];
pairs=AllPairs[Range[q]];
(*Filter 1: Remove pairs whose F-product has non-zero components over more than k-2 other eigenvectors*)
filtered1={};
Do[loc=Flatten[{pairs[[r]], Select[Range[q], Abs[Z[[r]][[#]]]>0&]}]//DeleteDuplicates;
If[Length[loc]<=k, AppendTo[filtered1,loc]], {r,Range[(q(q-1))/2]}];
Print[Length[filtered1]," candidate rows after first filter"];
(*Filter 2: Go through candidates at this stage and remove those which are missing a pair e.g. if F^(12)=Subscript[v, 3] but F^(13) is not among the candidates then (1,2,3) cannot be part of the same subalgebra*)
filtered2={};
commutingPairs={};
Do[If[Length[c]==2,
AppendTo[filtered2,c];
AppendTo[commutingPairs,c],
If[SubsetQ[filtered1[[;;,;;2]],AllPairs[Sort[c]]],AppendTo[filtered2,c]]],{c,filtered1}];
Print[Length[filtered2]," candidate rows after second filter"];
(*Improvement: do not compute anything for the subsets whose rank is too large*)
forbiddenCombinations={};
If[Length[commutingPairs]>0,
g=UndirectedGraph[#[[1]]->#[[2]]&/@commutingPairs,VertexLabels -> Placed["Name", Center],VertexLabelStyle -> Directive[Bold] ,VertexStyle->Yellow,VertexSize->Large];
Print[g];
Do[AppendTo[forbiddenCombinations,subgraph//VertexList//Sort],{k,Range[R+1,n-1]},{subgraph,FindIsomorphicSubgraph[g,CompleteGraph[k],All]}]
Print["Commuting subalgebras of dimension higher than ", R, ": ", forbiddenCombinations];
Print["An so(",n,") subalgebra cannot contain any of these subalgebras"];];
If[LastStep,
Cand=SubsetsExcluding[filtered2//Flatten//Sort//DeleteDuplicates,k,forbiddenCombinations];
Print["Checking ", Length[Cand]," possible ", k ,"-d subalgebras with rank \[LessEqual]",R,"..."];
(*Filter 3:*)
filtered3={};
Do[If[SubsetAnyQ[subset,forbiddenCombinations],Continue[],fprods=Select[filtered2,ContainsAny[AllPairs[subset],{#[[;;2]]}]&];
If[SubsetQ[subset,fprods[[;;,3;;]]//Flatten] && Length[fprods]==k (k-1)/2,AppendTo[filtered3,subset]]],{subset,Cand}];
If[Length[filtered3]>0,Do[Print[subalg, " is a LM-orthogonal ", k, "-d subalgebra!"],{subalg,filtered3}];
Return[(BasisFromIndices[Evecs,#]&)/@filtered3],Print["No LM-orthogonal ",k, "-d subalgebra!"];Return[{}]]])
