param n:= 10;
set I:= {1..n};		#Orden de los países: Argentina, Bolivia, Brazil, Chile, Colombia, Ecuador, Paraguay, Peru, Uruguay y Venezuela
set K:= {1..18};
set I_s:= {1,3};
set K_odd:= {1,3,5,7,9,11,13,15,17};
var x[I*I*K] binary;
var w[I*K] binary;
var y[I*K] binary;
param rondas_min_max:= 5;		#El tp sugiere estas cotas, pero podemos probar
param rondas_consecutivas_min_max:= 13;


minimize f : sum<i,k> in I*K_odd : (w[i,k]);

subto r1: forall <i,j> in I*I with i!=j: sum<k> in K with k<=n-1: (x[i,j,k] + x[j,i,k]) == 1 ;
subto r2: forall <i,j> in I*I with i!=j: sum<k> in K with k>n-1: (x[i,j,k] + x[j,i,k]) == 1 ;
subto r3: forall <i,j> in I*I with i!=j: sum<k> in K: (x[i,j,k]) == 1 ;
subto r4: forall <j,k> in I*K: sum<i> in I with i!=j: (x[i,j,k] + x[j,i,k]) == 1 ;

#Entiendo que el tp pide correr con y sin la condicion r5, porque dice: 
#"Correr ambas opciones, la que distingue a ARG y BRA para que no esten en la doble-fecha de nadie y la que no la tiene"
subto r5: forall <i,k> in (I-I_s)*K with k < card(K): sum<j> in I_s: (x[i,j,k] + x[j,i,k] + x[i,j,k+1] + x[j,i,k+1]) <= 1 ;

subto r6_i: forall <i> in I: sum<k> in K_odd: (y[i,k]) >= n/2-1 ;				
subto r6_ii: forall <i> in I: sum<k> in K_odd: (y[i,k]) <= n/2 ;	
subto r7: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[i,j,k] + x[j,i,k+1]) <= 1 + y[i,k] ;
subto r8: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[i,j,k]) >= y[i,k] ;
subto r9: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[j,i,k+1]) >= y[i,k] ;

subto r10: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[j,i,k] + x[j,i,k+1]) <= 1 + w[i,k] ;
subto r11: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[j,i,k]) >= w[i,k] ;
subto r12: forall <i,k> in I*K_odd: sum<j> in I with i!=j: (x[j,i,k+1]) >= w[i,k] ;

#Distintos esquemas
#Esquema espejado
#El esquema espejado queda infactible con el agregado de las condiciones H-A
#subto mirrored: forall <i,j,k> in I*I*K with i!=j and 1<=k and k<=n−1: x[i,j,k] == x[j,i,k+n−1] ;
 
#Por eso, se exploraron otros esquemas intentando mantener la idea de simetría
#Esquema francés
subto frances_i: forall <i,j,k> in I*I*K with i!=j and 2<=k and k<=n-1: x[i,j,1] == x[j,i,2*n-2] ; 
subto frances_ii: forall <i,j,k> in I*I*K with i!=j and 2<=k and k<=n-1: x[i,j,k] == x[j,i,k+n-2] ; 

#Esquema inglés
#subto ingles_i: forall <i,j,k> in I*I*K with i!=j and 2<=k and k<=n-2: x[i,j,n-1] == x[j,i,n] ; 
#subto ingles_ii: forall <i,j,k> in I*I*K with i!=j and 2<=k and k<=n-2: x[i,j,k] == x[j,i,k+n] ;

#Esquema invertido
#subto inverted: forall <i,j,k> in I*I*K with i!=j and 1<=k and k<=n-1: x[i,j,k] == x[j,i,2*n-1-k] ;

#Esquema back-to-back
#subto back_to_back: forall <i,j,k> in I*I*K_odd with i!=j: x[i,j,k] == x[j,i,k+1] ;

#Esquema min-max
#subto min_max_i: forall <i,j,k> in I*I*K with i!=j and k<=card(K)-rondas_min_max: sum<k_prima> in K with k<=k_prima and k_prima<=k+rondas_min_max: (x[i,j,k_prima] + x[j,i,k_prima]) <= 1 ;


#subto min_max_ii: forall <i,j,k> in I*I*K with i!=j : sum <k_prima> in K with ((k-rondas_consecutivas_min-max <= k_prima and 1 <= k_prima) and (k_prima <= (k+rondas_consecutivas_min-max) or k_prima <= 2*(n-1))) and k_prima != k : x[i,j,k_prima] >= x[j,i,k]

