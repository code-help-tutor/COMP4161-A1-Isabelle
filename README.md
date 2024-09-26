# COMP4161 T3/2024 Advanced Topics in Software Verification - Assignment 1

## 1. λ-Calculus (16 marks)
### (a) Simplify the term $(pq)(\lambda p\cdot(\lambda q\cdot(\lambda r\cdot(q(rp))))))))$ syntactically by applying the syntactic conventions and rules. Justify your answer. (2 marks)
1. First, we apply the application rule. The term is of the form $(M N)$ where $M = pq$ and $N=\lambda p\cdot(\lambda q\cdot(\lambda r\cdot(q(rp))))))))$.
   - When we apply $(M N)$ with $M = pq$ and $N=\lambda p\cdot(\lambda q\cdot(\lambda r\cdot(q(rp)))))))$, we substitute $p$ with $p$ (from $pq$) and $q$ with $q$ (from $pq$) in the body of $N$.
   - The body of $N$ is $\lambda q\cdot(\lambda r\cdot(q(rp)))))))$. Substituting $p$ and $q$ gives us $\lambda q\cdot(\lambda r\cdot(q(rp)))))))$ where $p$ and $q$ are the values from $pq$.
   - Now we have another application. The term is now $q(\lambda r\cdot(q(rp)))))))$ (because we applied the first substitution).
   - We again apply the application rule. Substitute $r$ with $r$ (whatever its value is in the context) in the body of $\lambda r\cdot(q(rp)))))))$.
   - The body becomes $(q(rp))))))$.
   - So the simplified term is $(q(rp))))))$.

### (b) Restore the omitted parentheses in the term $a(\lambda a b.(bc)a(bc))(\lambda b.cb)$ (but make sure you don’t change the term structure). (2 marks)
1. The term should be $a((\lambda a b.((b c)a(b c))))(\lambda b.c b))$.
   - The innermost lambda expression $\lambda a b.(bc)a(bc)$ needs its own parentheses around the body.
   - And the whole application of $a$ to the lambda expression and then to $(\lambda b.cb)$ also needs appropriate parentheses.

### (c) Find the normal form of $(\lambda f\cdot\lambda x\cdot f(fx))(\lambda g\cdot\lambda y\cdot g(g(gy)))))$. Justify your answer by showing the reduction sequence. Each step in the reduction sequence should be a single β-reduction step. Underline or otherwise indicate the redex being reduced for each step. (6 marks)
1. Let's start with the term $(\lambda f\cdot\lambda x\cdot f(fx))(\lambda g\cdot\lambda y\cdot g(g(gy)))))$.
   - The redex is $(\lambda f\cdot\lambda x\cdot f(fx))(\lambda g\cdot\lambda y\cdot g(g(gy)))))$. We substitute $f$ with $\lambda g\cdot\lambda y\cdot g(g(gy)))$ and $x$ with any value (let's say $z$ for simplicity, but it doesn't matter in this context as we are just reducing syntactically).
   - After the first β-reduction, we get $\lambda x\cdot(\lambda g\cdot\lambda y\cdot g(g(gy)))(\lambda g\cdot\lambda y\cdot g(g(gy))x)))$.
   - Now the new redex is $(\lambda g\cdot\lambda y\cdot g(g(gy)))(\lambda g\cdot\lambda y\cdot g(g(gy))x)))$. We substitute $g$ with $\lambda g\cdot\lambda y\cdot g(g(gy)))$ and $y$ with $x$.
   - After the second β-reduction, we get $\lambda y\cdot(\lambda g\cdot\lambda y\cdot g(g(gy)))(\lambda g\cdot\lambda y\cdot g(g(gy)))(\lambda g\cdot\lambda y\cdot g(g(gy))y)))$.
   - We can continue this process, but it becomes clear that the term will keep expanding and we won't reach a normal form in a finite number of steps. This is because the function $\lambda g\cdot\lambda y\cdot g(g(gy)))$ is being applied to itself repeatedly.

### (d) Recall the encoding of natural numbers in lambda calculus (Church Numerals) seen in the lecture:
   - $0\equiv\lambda fx,x$
   - $1\equiv\lambda fx.fx$
   - $2\equiv\lambda fx.f(fx)$
   - $3\equiv\lambda fx.f(f(fx))...$
Define `exp` where `exp m n` beta-reduces to the Church Numeral representing $m^{n}$. Provide a justification of your answer. (6 marks)
1. We want to define an `exp` function in lambda calculus. Let's first consider what the operation should do.
   - If we have $m$ and $n$ as Church Numerals, we want to apply the function $m$ times to another function, and then apply that result $n$ times to the argument $x$.
2. We define `exp` as follows:
   - `exp` ≡ $\lambda m n f x.m (n f) x$
3. Justification:
   - Let $m=\lambda f_m x_m.f_m^{m}(x_m)$ and $n=\lambda f_n x_n.f_n^{n}(x_n)$ (where $f_m^{m}(x_m)$ means applying $f_m$ to $x_m$ $m$ times and similarly for $n$).
   - First, we consider the inner application $n f$.
     - Substituting $f$ with $f$ and $x$ with $f$ in the body of $n$, we get $n f=\lambda x_n.f_n^{n}(f)$.
   - Then we apply $m$ to $(n f)$.
     - Substituting $f$ with $(n f)$ and $x$ with $x$ in the body of $m$, we get $m(n f)=\lambda x_m.(n f)^{m}(x_m)=\lambda x_m.(\lambda x_n.f_n^{n}(f))^{m}(x_m)$.
     - This means applying the function $n f$ (which is applying $f_n^{n}(f)$) $m$ times to $x_m$.
   - Finally, we apply the result to $x$.
     - So `exp m n f x` will result in applying the function $m$ times to $n f$ and then applying that result to $x$, which is equivalent to the Church Numeral representation of $m^{n}$.

## 2. Types (20 marks)
### (a) Provide the most general type for the term $\lambda a b c.a(x b b)(c b)$. Show a type derivation tree to justify your answer. Each node of the tree should correspond to the application of a single typing rule, and be labeled with the typing rule used. Under which contexts is the term type correct? (5 marks)
1. Type derivation tree:
   - Start with the root node representing the whole term $\lambda a b c.a(x b b)(c b)$.
   - Apply the rule for lambda abstraction. The type of $\lambda a b c.a(x b b)(c b)$ is of the form $\tau_1\to\tau_2\to\tau_3\to\tau_4$ where we need to find the types $\tau_1,\tau_2,\tau_3,\tau_4$.
   - For the first application $a(x b b)$, we know that $a$ has a type $\tau_1$ and $x b b$ must have a type that is compatible with the argument type of $a$. Let's assume $x$ has type $\sigma$ and $b$ has type $\rho$. Then $x b b$ has type $\sigma\to\rho\to\rho$. So the type of $a$ must be $\sigma\to\rho\to\rho\to\tau_2$.
   - For the second application $(c b)$, $c$ has type $\tau_3$ and $b$ has type $\rho$. So $\tau_3$ must be $\rho\to\tau_4$.
   - Combining these, the most general type is $(\sigma\to\rho\to\rho\to\tau_2)\to(\rho\to\tau_4)\to\tau_1\to\tau_2\to\tau_3\to\tau_4$.
   - The term is type correct under the context where the types of variables are assigned as described above (i.e., $x:\sigma, b:\rho, a:\sigma\to\rho\to\rho\to\tau_2, c:\rho\to\tau_4$).

### (b) Find a closed lambda term that has the following type:
   - $('a\Rightarrow'b)\Rightarrow('c\Rightarrow'a)\Rightarrow'c\Rightarrow'b$
(You don’t need to provide a type derivation, just the term). (4 marks)
1. The term $\lambda f g x.f(g x)$ has the given type.
   - Let's assume $f$ has type $('a\Rightarrow'b)$, $g$ has type $('c\Rightarrow'a)$, and $x$ has type $'c$.
   - Then $g x$ has type $'a$ (by applying the function $g$ of type $('c\Rightarrow'a)$ to $x$ of type $'c$).
   - Then $f(g x)$ has type $'b$ (by applying the function $f$ of type $('a\Rightarrow'b)$ to $g x$ of type $'a$).
   - So $\lambda f g x.f(g x)$ has the type $('a\Rightarrow'b)\Rightarrow('c\Rightarrow'a)\Rightarrow'c\Rightarrow'b$.

### (c) Explain why $\lambda x.xx$ is not typable. (3 marks)
1. The term $\lambda x.xx$ is not typable because when we try to assign a type to it, we run into a problem.
   - Let's assume $x$ has type $\tau$. Then the term $xx$ is applying the function $x$ to itself. But for a function application to be type correct, the type of the function (the first $x$) must be of the form $\sigma\to\rho$ and the type of the argument (the second $x$) must be $\sigma$.
   - In the case of $\lambda x.xx$, we have the same variable $x$ being both the function and the argument. If we assume $x:\tau$, then for $xx$ to be type correct, $\tau$ would need to be both $\sigma\to\rho$ and $\sigma$ simultaneously, which is not possible for a single type. So the term is not typable.

### (d) Find the normal form and its type of $(\lambda f x.f(x x))(\lambda y z.z)$. (3 marks)
1. First, we apply the function $(\lambda f x.f(x x))$ to $(\lambda y z.z)$.
   - The redex is $(\lambda f x.f(x x))(\lambda y z.z)$. We substitute $f$ with $\lambda y z.z$ and $x$ with any value (let's say $a$ for simplicity).
   - After the β-reduction, we get $\lambda x.(\lambda y z.z)(x x)$.
   - Now the new term is $\lambda x.z$.
   - The normal form is $\lambda x.z$.
   - The type of the original term $(\lambda f x.f(x x))$ is $\tau_1\to\tau_2\to\tau_3$ where $\tau_1$ is the type of $f$, $\tau_2$ is the type of $x$, and $\tau_3$ is the result type. If we assume $f:\sigma\to\rho, x:\tau$, then the type of $f(x x)$ is $\rho$ (assuming $x x$ has a compatible type). So the type of $(\lambda f x.f(x x))$ is $(\sigma\to\rho)\to\tau\to\rho$.
   - The term $(\lambda y z.z)$ has type $\sigma\to\tau\to\tau$. When we apply the first term to the second term, the resulting type is $\tau\to\tau$. So the type of the normal form $\lambda x.z$ is $\tau\to\tau$.

### (e) Is $(\lambda f x.f(x x))(\lambda y z.z)$ typable? Compare this situation with the Subject Reduction that you learned in the lecture. (5 marks)
1. The term $(\lambda f x.f(x x))(\lambda y z.z)$ is typable.
   - As we saw in part (d), the type of $(\lambda f x.f(x x))$ is $(\sigma\to\rho)\to\tau\to\rho$ and the type of $(\lambda y z.z)$ is $\sigma\to\tau\to\tau$. The types are compatible for application.
2. Regarding Subject Reduction:
   - Subject Reduction states that if a term $M$ has a type $\tau$ and $M$ reduces to $N$ (i.e., $M\to N$), then $N$ also has a type and the type is related to $\tau$.
   - In this case, we started with $(\lambda f x.f(x x))(\lambda y z.z)$ and reduced it to $\lambda x.z$. The original term had a certain type as we determined, and the reduced term also has a type.
   - The type of the reduced term is a consequence of the reduction and the typing rules. The fact that the term can be typed before and after reduction is consistent with the idea of Subject Reduction. If the term was not typable before reduction and became typable after reduction (or vice versa), it would violate the principle of Subject Reduction. Here, the typing is consistent throughout the reduction process, which aligns with the concept of Subject Reduction.

## 3. Propositional Logic (29 marks)
### (a) $x\to\neg\neg x$ (3 marks)
1. Proof:
   - We use the rule `notI` (introduction of negation).
   - Assume $x$.
   - We want to show $\neg\neg x$.
   - Assume $\neg x$ (for the purpose of `notI`).
   - This leads to a contradiction since we have assumed $x$ and now $\neg x$.
   - By `notI`, we can conclude $\neg\neg x$.
   - So $x\to\neg\neg x$ holds by the rule `impI` (introduction of implication).

### (b) $(X\to Y\to\neg X)\to X\to\neg Y$ (3 marks)
1. Proof:
   - Assume $(X\to Y\to\neg X)$.
   - Also assume $X$.
   - We want to show $\neg Y$.
   - From $(X\to Y\to\neg X)$ and $X$, by `impE` (elimination of implication), we get $Y\to\neg X$.
   - Since we have $X$ and $Y\to\neg X$, and assuming $Y$ (for the purpose of `notI`), we get $\neg X$ by `impE`.
   - But we already have $X$, so this is a contradiction.
   - By `notI`, we can conclude $\neg Y$.
   - So $(X\to Y\to\neg X)\to X\to\neg Y$ holds by `impI`.

### (c) $\neg\neg A\to A$ (4 marks)
1. Proof:
   - Assume $\neg\neg A$.
   - Assume $\neg A$ (for the purpose of `notI`).
   - This leads to a contradiction since we have $\neg\neg A$ and now $\neg A$.
   - By `notI`, we can conclude $A$.
   - So $\neg\neg A\to A$ holds by `impI`.

### (d) $\neg(A\land B)\to\neg A\vee\neg B$ (4 marks)
1. Proof:
   - Assume $\neg(A\land B)$.
   - We want to show $\neg A\vee\neg B$.
   - Assume $\neg(\neg A\vee\neg B)$ (for the purpose of `notI`).
   - By De Morgan's law, $\neg(\neg A\vee\neg B)$ is equivalent to $A\land B$.
   - But we have assumed $\neg(A\land B)$, so this is a contradiction.
   - By `notI`, we can conclude $\neg A\vee\neg B$.
   - So $\neg(A\land B)\to\neg A\vee\neg B$ holds by `impI`.

### (e) $\neg(A\to B)\to A$ (4 marks)
1. Proof:
   - Assume $\neg(A\to B)$.
   - Assume $\neg A$ (for the purpose of `notI`).
   - Since $\neg A$, then $A\to B$ holds vacuously (if the antecedent is false, the implication is true).
   - But we have assumed $\neg(A\to B)$, so this is a contradiction.
   - By `notI`, we can conclude $A$.
   - So $\neg(A\to B)\to A$ holds by `impI`.

### (f) (continued)
1. Proof of $\neg(A\vee B)\to(\neg A\land\neg B)$:
   - Assume $\neg(A\vee B)$.
   - Assume $A$ (for the purpose of `notI`).
   - Then $A\vee B$ holds, which contradicts $\neg(A\vee B)$.
   - So by `notI`, we can conclude $\neg A$.
   - Assume $B$ (for the purpose of `notI`).
   - Then $A\vee B$ holds, which contradicts $\neg(A\vee B)$.
   - So by `notI`, we can conclude $\neg B$.
   - By `conjI` (introduction of conjunction), we have $\neg A\land\neg B$.
   - So $(\neg A\land\neg B)=(\neg(A\vee B))$ holds by the two implications we proved.

### (g) $(A\to B)\to((B\to C)\to A)\to B$ (5 marks)
1. Proof:
   - Assume $A\to B$.
   - Also assume $(B\to C)\to A$.
   - We want to show $B$.
   - Assume $\neg B$ (for the purpose of `notI`).
   - From $A\to B$ and $\neg B$, by `notE` (elimination of negation), we can conclude $\neg A$.
   - From $(B\to C)\to A$ and $\neg A$, by `notE`, we can conclude $\neg(B\to C)$.
   - By the definition of implication, $\neg(B\to C)$ is equivalent to $B\land\neg C$.
   - By `conjunct1`, we have $B$, which contradicts $\neg B$.
   - By `notI`, we can conclude $B$.
   - So $(A\to B)\to((B\to C)\to A)\to B$ holds by `impI`.

## 4. Higher-Order Logic (35 marks)
### (a) $(\forall x.\neg Px)=(\nexists x.Px)$ (4 marks)
1. Proof:
   - We want to show $(\forall x.\neg Px)\to(\nexists x.Px)$ and $(\nexists x.Px)\to(\forall x.\neg Px)$.
2. Proof of $(\forall x.\neg Px)\to(\nexists x.Px)$:
   - Assume $\forall x.\neg Px$.
   - Assume $\exists x.Px$ (for the purpose of `notI`).
   - By `exE` (elimination of existential quantifier), there exists a particular $a$ such that $Pa$.
   - But from $\forall x.\neg Px$, we have $\neg Pa$, which is a contradiction.
   - By `notI`, we can conclude $\neg\exists x.Px$, which is equivalent to $\forall x.\neg Px$.
3. Proof of $(\nexists x.Px)\to(\forall x.\neg Px)$:
   - Assume $\neg\exists x.Px$.
   - We want to show $\forall x.\neg Px$.
   - Let $a$ be an arbitrary element.
   - Assume $Pa$ (for the purpose of `notI`).
   - Then $\exists x.Px$, which contradicts $\neg\exists x.Px$.
   - By `notI`, we can conclude $\neg Pa$.
   - Since $a$ was arbitrary, we have $\forall x.\neg Px$.
   - So $(\forall x.\neg Px)=(\nexists x.Px)$.

### (b) $(\exists x y.Pxy)=(\exists y x.Pxy)$ (4 marks)
1. Proof:
   - We know that the order of existential quantifiers does not matter in this case.
   - Assume $\exists x y.Pxy$.
   - By `exE`, there exist $a$ and $b$ such that $Pab$.
   - Then $\exists y x.Pxy$ holds because we have found $b$ and $a$ such that $Pxy$ (with $x = a$ and $y = b$).
   - Conversely, assume $\exists y x.Pxy$.
   - By `exE`, there exist $b$ and $a$ such that $Pab$.
   - Then $\exists x y.Pxy$ holds.
   - So $(\exists x y.Pxy)=(\exists y x.Pxy)$.

### (c) $(\exists x.Px\to Q)=((\forall x.Px)\to Q)$ (7 marks)
1. Proof:
   - First, we prove $(\exists x.Px\to Q)\to((\forall x.Px)\to Q)$.
   - Assume $\exists x.Px\to Q$.
   - Assume $\forall x.Px$.
   - We want to show $Q$.
   - From $\forall x.Px$, by `allE` (elimination of universal quantifier), we can get $Pa$ for any particular $a$.
   - Since $\exists x.Px$ holds (because we have $Pa$ for some $a$), and $\exists x.Px\to Q$, by `impE`, we can conclude $Q$.
   - So $(\exists x.Px\to Q)\to((\forall x.Px)\to Q)$.
2. Now, we prove $((\forall x.Px)\to Q)\to(\exists x.Px\to Q)$.
   - Assume $(\forall x.Px)\to Q$.
   - We want to show $\exists x.Px\to Q$.
   - Assume $\exists x.Px$.
   - By `exE`, there exists a particular $a$ such that $Pa$.
   - Now assume $\neg Q$ (for the purpose of `notI`).
   - Since we have $Pa$ and $\neg Q$, and assuming $\forall x.Px$ (for the purpose of `notI`), we get a contradiction because $(\forall x.Px)\to Q$.
   - By `notI`, we can conclude $Q$.
   - So $\exists x.Px\to Q$.
   - Therefore, $(\exists x.Px\to Q)=((\forall x.Px)\to Q)$.

### (d) $((\forall x.Px)\to(\exists x.Qx))=(\exists x.Px\to Qx)$ (7 marks)
1. Proof:
   - First, we prove $((\forall x.Px)\to(\exists x.Qx))\to(\exists x.Px\to Qx)$.
   - Assume $(\forall x.Px)\to(\exists x.Qx)$.
   - We want to show $\exists x.Px\to Qx$.
   - Assume $\exists x.Px$.
   - By `exE`, there exists a particular $a$ such that $Pa$.
   - Now assume $\neg Qa$ (for the purpose of `notI`).
   - Assume $\forall x.Px$.
   - From $\forall x.Px\to(\exists x.Qx)$ and $\forall x.Px$, by `impE`, we get $\exists x.Qx$.
   - By `exE`, there exists a $b$ such that $Qb$.
   - But we have assumed $\neg Qa$, so this is a contradiction.
   - By `notI`, we can conclude $Qa$.
   - So $\exists x.Px\to Qx$.
2. Now, we prove $(\exists x.Px\to Qx)\to((\forall x.Px)\to(\exists x.Qx))$.
   - Assume $\exists x.Px\to Qx$.
   - We want to show $(\forall x.Px)\to(\exists x.Qx)$.
   - Assume $\forall x.Px$.
   - We want to show $\exists x.Qx$.
   - Assume $\neg\exists x.Qx$ (for the purpose of `notI`).
   - By `notE`, this is equivalent to $\forall x.\neg Qx$.
   - Now assume $Pa$ for a particular $a$ (since $\forall x.Px$).
   - From $\exists x.Px\to Qx$ and $Pa$, we should have $Qa$.
   - But we have $\forall x.\neg Qx$, which is a contradiction.
   - By `notI`, we can conclude $\exists x.Qx$.
   - So $((\forall x.Px)\to(\exists x.Qx))=(\exists x.Px\to Qx)$.

### (e) $\forall x.\neg Rx\to R(Mx)\Rightarrow\forall x.Rx\vee R(Mx)$ (6 marks)
1. Proof:
   - Assume $\forall x.\neg Rx\to R(Mx)$.
   - We want to show $\forall x.Rx\vee R(Mx)$.
   - Let $a$ be an arbitrary element.
   - We consider two cases:
     - Case 1: Assume $\neg Ra$.
       - From $\forall x.\neg Rx\to R(Mx)$, by `allE`, we have $\neg Ra\to R(Ma)$.
       - Since we have assumed $\neg Ra$, by `impE`, we get $R(Ma)$.
       - Then $Ra\vee R(Ma)$ holds by `disjI2` (introduction of disjunction).
     - Case 2: Assume $Ra$.
       - Then $Ra\vee R(Ma)$ holds by `disjI1` (introduction of disjunction).
   - Since $a$ was arbitrary, we have $\forall x.Rx\vee R(Mx)$ by `allI` (introduction of universal quantifier).

### (f) $\llbracket\forall x.\neg Rx\to R(Mx);\exists x.Rx\rrbracket\Rightarrow\exists x.Rx\land R(M(Mx))$ (7 marks)
1. Proof:
   - Assume $\forall x.\neg Rx\to R(Mx)$ and $\exists x.Rx$.
   - By `exE`, there exists a particular $a$ such that $Ra$.
   - From $\forall x.\neg Rx\to R(Mx)$, by `allE`, we have $\neg Ra\to R(Ma)$.
   - Now assume $\neg R(M(Ma))$ (for the purpose of `notI`).
   - Since $Ra$, we have $\neg\neg Ra$.
   - From $\neg Ra\to R(Ma)$ and $\neg\neg Ra$, by `mp` (modus ponens), we get $R(Ma)$.
   - Now assume $\neg R(Ma)$ (for the purpose of `notI`).
   - Since $\neg Ra\to R(Ma)$ and $\neg R(Ma)$, we have $\neg\neg Ra$ by `notE`.
   - But we have $Ra$, which is a contradiction. So we can conclude $R(Ma)$.
   - Now assume $\neg Ra$ (for the purpose of `notI`).
   - Since $\neg Ra\to R(Ma)$ and $\neg Ra$, we have $R(Ma)$.
   - Then assume $\neg R(M(Ma))$ (for the purpose of `notI`).
   - Since $\neg Ra\to R(Ma)$ and $R(Ma)$, we have $\neg\neg Ra$ by `notE`.
   - But we have $Ra$, which is a contradiction. So we can conclude $R(M(Ma))$.
   - So we have $Ra\land R(M(Ma))$.
   - Since $a$ was obtained from $\exists x.Rx$, we have $\exists x.Rx\land R(M(Mx))$ by `exI` (introduction of existential quantifier).
# COMP4161 A1 Isabelle

# CS Tutor | 计算机编程辅导 | Code Help | Programming Help

# WeChat: cstutorcs

# Email: tutorcs@163.com

# QQ: 749389476

# 非中介, 直接联系程序员本人
