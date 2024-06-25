(* ::Package:: *)

(***** General linear algebra functions ******)
e[i_]:=SparseArray[{{i}->1,{24}->0}]//Normal;


(* ::Input::Initialization:: *)
(***** General su(N) functions *****)


(* ::Input::Initialization:: *)
(*Commutator*)
Comm[x_,y_]:=x . y-y . x


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
f[N_]:=Table[-I/4 Tr[(\[Lambda][i,N] . \[Lambda][j,N]-\[Lambda][j,N] . \[Lambda][i,N]) . \[Lambda][k,N]],{i,1,N^2-1},{j,1,N^2-1},{k,1,N^2-1}]//Simplify;


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
Fprod[a_,b_]:=(dim=Sqrt[Dimensions[a][[1]]+1];If[dim\[Element]Integers && dim==Sqrt[Dimensions[b][[1]]+1],f[dim] . b . a//Chop,Print["Bad vector dimension. Expected two vectors of \!\(\*SuperscriptBox[TemplateBox[{},\n\"Reals\"], \(\*SuperscriptBox[\(N\), \(2\)] - 1\)]\)"]])


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
\[CapitalLambda][N_,randomCouplings_,randomLowerBlock_]:=(If[randomLowerBlock, lowerBlock=RandomReal[{-4Pi,4Pi},{1/2 N(N+1)-1,1/2 N(N+1)-1}1];lowerBlock=1/2 (lowerBlock+Transpose[lowerBlock]),lowerBlock=IdentityMatrix[1/2 N(N+1)-1]];
CSb=CSblock[N];
L=ArrayFlatten[{{CSb,ConstantArray[0,{1/2 N(N-1),1/2 N(N+1)-1}]},{ConstantArray[0,{1/2 N(N+1)-1,1/2 N(N-1)}],lowerBlock}}];
If[randomCouplings,L/.Table[Variables[CSb][[i]]->RandomReal[{-4Pi,4Pi}],{i,1,Binomial[N,4]}],L])


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


(*Given 6 matrices, checks if they satisfy the commutation relations of SO(3)+SO(3)*)


SatisfySO3SO3[Am_,Bm_,Cm_,Ap_,Bp_,Cp_]:=(
K=Sqrt[2]*Sqrt[Tr[Am . Am]/2];
 d=Min[Comm[Am,Bm]-K*I*Cm//Norm,Comm[Am,Bm]+K*I*Cm//Norm ];
d+=Min[Comm[Bm,Cm]-K*I*Am//Norm,Comm[Bm,Cm]+K*I*Am//Norm ];
d+=Min[Comm[Cm,Am]-K*I*Bm//Norm,Comm[Cm,Am]+K*I*Bm//Norm ];
 d+=Min[Comm[Ap,Bp]-K*I*Cp//Norm,Comm[Ap,Bp]+K*I*Cp//Norm ];
d+=Min[Comm[Bp,Cp]-K*I*Ap//Norm,Comm[Bp,Cp]+K*I*Ap//Norm ];
d+=Min[Comm[Cp,Ap]-K*I*Bp//Norm,Comm[Cp,Ap]+K*I*Bp//Norm ];
 d+=(Comm[Am,Ap]//Norm)+(Comm[Am,Bp]//Norm)+(Comm[Am,Cp]//Norm);
d+=(Comm[Bm,Ap]//Norm)+(Comm[Bm,Bp]//Norm)+(Comm[Bm,Cp]//Norm);
d+=(Comm[Cm,Ap]//Norm)+(Comm[Cm,Bp]//Norm)+(Comm[Am,Cp]//Norm);
Chop[d]==0)


(* ::Input::Initialization:: *)



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


(* ::Input::Initialization:: *)
(**********)
