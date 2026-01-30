r"""
Conditional Oriented Matroids

Conditional oriented matroids are abstractions for diverse mathematical objects like apartments of hyperplane arrangements, and partial cubes with gated antipodal subgraphs. They are common generalizations of oriented matroids and lopsided systems in particular. The following programs construct and manipulate these objects. Among others, functions computing the Varchenko determinant of a conditional oriented matroid, and resolving the Aguiar-Mahajan linear system of an oriented matroid are programmed.

REFERENCES: For more information on conditional oriented matroids, see [BCK2018]_.

AUTHOR:

- Hery Randriamaro (2023-11-20): initial version

"""

# *************************************************************************************
#       Copyright (C) 2023 Hery Randriamaro <hery.randriamaro@mathematik.uni-kassel.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# *************************************************************************************




# 1 Sign Vectors



r"""
Let `E` be a finite set. A sign vector is an element of `\{-1,\,0,\,1\}^E`.
"""


def isSignVector(X):
    r"""
    Return True if `-X` is a sign vector, otherwise False.
    
    INPUT:
    
    - ``X`` -- a sign vector
    
    EXAMPLES::
    
        sage: isSignVector((0, 1, -1, -1, 0, 0, 1))
        True
    """
    if isinstance(X, tuple):
        b = True
        for i in range(len(X)):
            if X[i] not in {-1, 0, 1}:
                b = False
                break
    else:
        b = False
    return b


def neg(X):
    r"""
    Return the negative `-X` of a sign vector `X`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    
    .. MATH::
    
        -X := (-X_e\ |\ e \in E)
    
    EXAMPLES::
    
        sage: neg((0, 1, -1, -1, 0, 0, 1))
        (0, -1, 1, 1, 0, 0, -1)
    """
    if not isSignVector(X):
        raise ValueError(f"a sign vector expected, but got {X}")
    return tuple(-X[i] for i in range(len(X)))

    
def zero(X):
    r"""
    Return the zero set `X^0` of a sign vector `X`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    
    .. MATH::
    
        X^0 := \{e \in E\ |\ X_e = 0\}
    
    EXAMPLES::
    
        sage: zero((0, 1, -1, -1, 0, 0, 1))
        {0, 4, 5}
    """
    if not isSignVector(X):
        raise ValueError(f"a sign vector expected, but got {X}")
    z = set()
    for i in range(len(X)):
        if X[i] == 0:
            z = z.union({i})
    return z
 
 
def support(X):
    r"""
    Return the support `\underline{X}` of a sign vector `X`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    
    .. MATH::
    
        \underline{X} := E \setminus X^0
        
    EXAMPLES::
    
        sage: support((0, 1, -1, -1, 0, 0, 1))
        {1, 2, 3, 6}
    """
    if not isSignVector(X):
        raise ValueError(f"a sign vector expected, but got {X}")
    s = set()
    for i in range(len(X)):
        if X[i] in {-1, 1}:
            s = s.union({i})
    return s


def separation(X, Y):
    r"""
    Return the separation set `\mathrm{S}(X,\,Y)` of two sign vectors `X` and `Y`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    - ``Y`` -- a sign vector
    
    .. MATH::
    
        \mathrm{S}(X,\,Y) := \big\{e \in E\ \big|\ X_e = -Y_e \neq 0\big\}
        
    EXAMPLES::
    
        sage: separation((1, -1, 0, 0, 1), (0, 1, 0, 1, -1))
        {1, 4}
    """
    if not (isSignVector(X) and isSignVector(Y) and len(X) == len(Y)):
        raise ValueError(f"two sign vectors with same length expected, but got {X} and {Y}")
    s = set()
    for i in range(len(X)):
        if X[i] in set([-1, 1]):
            if X[i] == -Y[i]:
                s = s.union({i})
    return s
 
 
def composition(X, Y):
    r"""
    Return the composition `X \circ Y` of the sign vectors `X` and `Y`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    - ``Y`` -- a sign vector
    
    .. MATH::
    
        \forall e \in E,\,
        (X \circ Y)_e := \begin{cases} X_e & \text{if}\ X_e \neq 0, \\
        Y_e & \text{otherwise}.
        
    EXAMPLES::
    
        sage: composition((1, -1, 0, 0, 1), (0, 1, 0, 1, -1))
        (1, -1, 0, 1, 1)
    """
    if not (isSignVector(X) and isSignVector(Y) and len(X) == len(Y)):
        raise ValueError(f"two sign vectors with same length expected, but got {X} and {Y}")
    def sigma(a, b):
        if a == 0:
            return b
        else:
            return a
    return tuple(sigma(X[i], Y[i]) for i in range(len(X)))
 

def prec(X, Y):
    r"""
    Return whether `X \preceq Y` for the partial order `\preceq`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    - ``Y`` -- a sign vector
    
    .. MATH::
    
        \forall X, Y \in \mathcal{L}:\ X \preceq Y \ \Longleftrightarrow \ \forall e \in E,\, X_e \in \{0,\, Y_e\}
        
    EXAMPLES::
    
        sage: prec((1, -1, 0, 0, 1), (0, 1, 0, 1, -1))
        False
    """
    if not (isSignVector(X) and isSignVector(Y) and len(X) == len(Y)):
        raise ValueError(f"two sign vectors with same length expected, but got {X} and {Y}")
    b = True
    for i in range(len(X)):
        b = b and (X[i] in {0, Y[i]})
    return b


class VariableGenerator(object):
    def __init__(self, prefix):
        self.__prefix = prefix
    @cached_method
    def __getitem__(self, key):
        return SR.var("%s%s"%(self.__prefix,key))
a = VariableGenerator('a')
b = VariableGenerator('b')


def v(X, Y):
    r"""
    Return the Aguiar-Mahajan distance between two sign vectors.
    
    INPUT:
    
    - ``X`` -- a sign vector
    - ``Y`` -- a sign vector
    
    .. MATH::
    
        `\mathrm{v}(X,\,Y) := \prod_{e \in \mathrm{S}(X,\,Y)} q_{e,X_e}` with `q_{e,X_e} = ae` if `X_e = -1` and `q_{e,X_e} = be` otherwise
        
    EXAMPLES::
    
        sage: v((1, -1, -1, 1, 1), (-1, -1, 1, 0, -1))
        a2*b0*b4
    """
    if not (isSignVector(X) and isSignVector(Y) and len(X) == len(Y)):
        raise ValueError(f"two sign vectors with same length expected, but got {X} and {Y}")
    def q(k, l):
        if l == -1:
            return(a[k])
        if l == 1:
            return(b[k])
    x=1
    for i in separation(X, Y):
        x = x*q(i, X[i])
    return x


def restriction(X, A):
    r"""
    Return the restriction `X \setminus A` of a sign vector `X` relative to a set `A`.
    
    INPUT:
    
    - ``X`` -- a sign vector
    - ``A`` -- a set
    
    .. MATH::
    
        X \setminus A \in \{-1,\,0,\,1\}^{E \setminus A},\, (X \setminus A)_e = X_e, \, \forall e \in E \setminus A
        
    EXAMPLES::
    
        sage: restriction((1, -1, 0, 0, 1), {1, 3, 4})
        (1, 0)
    """
    if not isSignVector(X):
        raise ValueError(f"a sign vector expected, but got {X}")
    return tuple(X[i] for i in set(range(len(X))).difference(A))



# 2 Sign Systems



r"""
A sign system is a pair `(E,\,\mathcal{L})` containing a finite set `E` and a subset `\mathcal{L}` of `\{-1,\,0,\,1\}^E`. For easy of programming, we assume a sign system to be a subset of `\{-1,\,0,\,1\}^E`.
"""

 
 
import random


class System:
    def __init__(self, vectorset):
        if not isinstance(vectorset, set):
            raise ValueError(f"a set expected, got {vectorset}")
        else:
            for V in vectorset:
                if not isSignVector(V):
                    raise ValueError(f"sign vectors expected, but got {V}")
        if vectorset != set():
            V = random.choice(list(vectorset))
            for W in vectorset:
                if len(V) != len(W):
                    raise ValueError(f"sign vectors with same length expected, but got {V} and {W}")
        self._vectorset = vectorset


    def __str__(self):
        r"""
        Print the sign system `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a sign system
    
        EXAMPLES::
    
            sage: L = System({(1, -1, 0, 0, 1), (0, 1, 1, -1, 0), (1, 1, 1, -1, 0), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1)})
            sage: L.__str__()
            'System({(1, 1, 1, -1, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (0, 1, 1, -1, 0), (1, -1, 0, 0, 1)})'
        """
        return f"System({self._vectorset})"
        

    def isSystemConform(self, X):
        r"""
        Return whether the sign vector `X` is maximal in this sign system `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a sign system
        - ``X`` -- a sign vector
    
        EXAMPLES::
    
            sage: L = System({(1, -1, 0, 0, 1), (0, 1, 1, -1, 0), (1, 1, 1, -1, 0), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1)})
            sage: X = (1, -1, 1, -1, 1)
            sage: L.isSystemConform(X)
            True
        """
        if not isSignVector(X):
            raise ValueError(f"a sign vector expected, but got {X}")
        else:
            if self._vectorset == set():
                return False
            else:
                V = random.choice(list(self._vectorset))
                if len(V) != len(X):
                    raise ValueError(f"sign vectors with same length expected, but got {self} and {X}")
                else:
                    return True


    def ismax(self, X):
        r"""
        Return whether the sign vector `X` is maximal in the sign system `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a sign system
        - ``X`` -- a sign vector
    
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: X = (1, -1, 1, -1, 0)
            sage: L.ismax(X)
            True
        """
        if not self.isSystemConform(X):
            return False
        else:
            b = True
            if X in self._vectorset:
                L = self._vectorset
                for Y in L.difference({X}):
                    b = b and not prec(X, Y)
            else:
                b = False
            return b


    def face(self, X):
        r"""
        Return the face `\mathrm{F}(X)` of a sign vector `X` in a sign system `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a sign system
        - ``X`` -- a sign vector
    
        .. MATH::
    
            \mathrm{F}(X) := \{Y \in \mathcal{L}\ |\ X \preceq Y\}
        
        EXAMPLES::
    
            sage: L = System({(1, -1, 0, 0, 1), (0, 1, 1, -1, 0), (1, 1, 1, -1, 0), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1)})
            sage: X = (0, 1, 0, 0, 0)
            sage: L.face(X).__str__()
            'System({(1, 1, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1), (0, 1, 0, 0, 1), (0, 1, 1, -1, 0)})'
        """
        if not self.isSystemConform(X):
            return System(set())
        else:
            S = set()
            for Y in self._vectorset:
                if prec(X, Y):
                    S = S.union({Y})
            return System(S)


    def fiber(self, X, A):
        r"""
        Return the fiber `\mathrm{F}(X,\,A)` in a sign system `\mathcal{L}` relative to a sign vector `X` and a set `A`.
    
        INPUT:
    
        - ``L`` -- a sign system
        - ``X`` -- a sign vector
        - ``A`` -- a set
    
        .. MATH::
    
            \mathrm{F}(X,\,A) := \{Y \in \mathcal{L}\ |\ Y \setminus A = X \setminus A\}
        
        EXAMPLES::
    
            sage: L = System({(1, -1, 0, 0, 1), (0, 1, 1, -1, 0), (1, 1, 1, -1, 0), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1)})
            sage: X = (1, -1, 0, 0, 1)
            sage: A = {1, 3, 4}
            sage: L.fiber(X, A).__str__()
            'System({(1, 1, 0, -1, -1), (1, -1, 0, 0, 1)})'
        """
        if not self.isSystemConform(X):
            return System(set())
        else:
            S = set()
            for Y in self._vectorset:
                if restriction(Y, A) == restriction(X, A):
                    S = S.union({Y})
            return System(S)

        
    def isFaceSymmetry(self):
        r"""
        Return if the sign system `\mathcal{L}` possesses the face symmetry condition.
    
        INPUT:
    
        - ``L`` -- a sign system
    
        EXAMPLES::
    
            sage: L = System({(1, -1, 0, 0, 1), (0, 1, 1, -1, 0), (1, 1, 1, -1, 0), (0, 1, 0, 0, 1), (0, 0, 1, -1, 0), (0, 1, 0, 0, 0), (1, 1, 0, -1, -1), (0, 1, 0, 1, -1)})
            sage: L.isFaceSymmetry()
            False
        """
        b = True
        for X in self._vectorset:
            for Y in self._vectorset:
                b = b & (composition(X, neg(Y)) in self._vectorset)
        return b


    def isStrongElimination(self):
        r"""
        Return if the sign system `\mathcal{L}` possesses the strong elimination condition.
    
        INPUT:
    
        - ``L`` -- a sign system
    
        EXAMPLES::
    
            sage: L = System({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})
            sage: L.isStrongElimination()
            True
        """
        b = True
        for X in self._vectorset:
            for Y in self._vectorset:
                S = set()
                F = self.fiber(composition(X, Y), separation(X, Y))
                for Z in F._vectorset:
                    S = S.union(zero(Z))
                b = b & (S.intersection(separation(X, Y)) == separation(X, Y))
        return b



# 3 Conditional Oriented Matroids



r"""
A conditional oriented matroid is a sign system possessing the face symmetry and strong elimination conditions.
"""



class COM(System):
    def __init__(self, vectorset):
        System.__init__(self, vectorset)
        if not self.isFaceSymmetry():
            raise ValueError(f"a system possessing the face symmetry condition expected, but got {vectorset}")
        if not self.isStrongElimination():
            raise ValueError(f"a system possessing the strong elimination condition expected, but got {vectorset}")
        self._vectorset = vectorset


    def __str__(self):
        r"""
        Print the conditional oriented matroid `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: L.__str__()
            'COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})'
        """
        return f"COM({self._vectorset})"


    def tope(self):
        r"""
        Return the tope set `\mathcal{T}` of a conditional oriented matroid `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        .. MATH::
    
            \mathcal{T} := \{X \in \mathcal{L}\ |\ \nexists Y \in \mathcal{L},\, X \prec Y\}
        
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: L.tope()
            {(1, -1, -1, -1, 0), (1, -1, -1, 1, 0), (1, -1, 1, 1, 0), (1, 1, 1, 1, 0), (1, -1, 1, -1, 0)}
        """
        S = set()
        for X in self._vectorset:
            if self.ismax(X):
                S = S.union({X})
        return S


    def deletion(self, A):
        r"""
        Return the deletion `\mathcal{L}\A` of a conditional oriented matroid `\mathcal{L}` relative to a set `A`.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
        - ``A`` -- a set
    
        .. MATH::
    
            `\mathcal{L} \setminus A = \{X \setminus A\ |\ X \in \mathcal{L}\}`
        
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: A = {2, 4}
            sage: L.deletion({2, 4}).__str__()
            'COM({(1, 0, 1), (1, -1, 0), (1, -1, 1), (1, 1, 1), (1, -1, -1)})'
        """
        return COM({restriction(X, A) for X in self._vectorset})


    def contraction(self, A):
        r"""
        Return the contraction `\mathcal{L}/A` of a conditional oriented matroid `\mathcal{L}` relative to a set `A`.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
        - ``A`` -- a set
    
        .. MATH::
    
            `\mathcal{L}/A := \{X \setminus A\ |\ X \in \mathcal{L},\, \underline{X} \cap A = \varnothing\}`
        
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: A = {2, 4}
            sage: L.contraction(A).__str__()
            'COM({(1, -1, 0), (1, -1, 1), (1, -1, -1)})'
        """
        S = set()
        for X in self._vectorset:
            if support(X).intersection(A) == set():
                S = S.union({restriction(X, A)})
        return COM(S)


    def coloop(self):
        r"""
        Return the coloop set for a conditional oriented matroid `\mathcal{L}`.
        
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        .. MATH::
        
            An element `e \in E` is a coloop if `\{X_e\ |\ X \in \mathcal{L}\} \subseteq \big\{\{-1\},\, \{0\},\, \{1\}\big\}`.
                
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: L.coloop()
            {0, 4}
        """
        S = set()
        V = random.choice(list(self._vectorset))
        for e in range(len(V)):
            Xe = {X[e] for X in self._vectorset}
            if len(Xe) == 1:
                S = S.union({e})
        return S


    def parallelElement(self):
        r"""
        Return the list of parallel elements for a conditional oriented matroid `\mathcal{L}`.    
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        .. MATH::
            
            Two elements `e,f \in E` are parallel if either `X_e = X_f` for all `X \in \mathcal{L}`, or `X_e = -X_f` for all `X \in \mathcal{L}.  
                          
        EXAMPLES::
    
            sage: L = COM({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})
            sage: L.parallelElement()
            [{0, 4}, {1}, {2}, {3}]
        """
        def parallel(M, e, f):
            Le = tuple(X[e] for X in M)
            Lf = tuple(X[f] for X in M)
            return (Le==Lf) | (Le==neg(Lf))
        E = set(range(len(random.choice(list(self._vectorset)))))
        P = []
        while len(E) > 0:
            for e in E:
                Pe = set()
                for f in E:
                    if parallel(self._vectorset, e, f):
                        Pe = Pe.union({f})
                if len(Pe) > 0:
                    P.append(Pe)
                E = E.difference(Pe)
        return P


    def simplification(self):
        r"""
        Return a simplification of a conditional oriented matroid `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
            
        .. MATH::
            
            A conditional oriented matroid is simple if it has neither coloops nor distinct parallel elements.
            A homomorphism between two conditional oriented matroids `(E,\, \mathcal{L})` and `(F,\, \mathcal{M})` is a function `h: \mathcal{L} \rightarrow \mathcal{M}` such that `\forall X, Y \in \mathcal{L},\ X \preceq Y \Longrightarrow h(X) \preceq h(Y)`.
            One says that the homomorphism `h` is an isomorphism if it is additionally bijective.
            A simplification of `(E,\, \mathcal{L})` is a simple conditional oriented matroid which is isomorphic to `(E,\, \mathcal{L})`.
                    
        EXAMPLES::
    
            sage: L = COM({(1, -1, 1, 0, 0), (1, -1, 1, -1, 0), (1, -1, 1, 1, 0), (1, -1, 1, 0, -1), (1, -1, 1, 0, 1), (1, -1, 1, -1, -1), (1, -1, 1, -1, 1), (1, -1, 1, 1, -1), (1, -1, 1, 1, 1)})
            sage: L.simplification().__str__()
            'COM({(0, 1), (-1, -1), (0, 0), (-1, 1), (1, 1), (1, -1), (-1, 0), (1, 0), (0, -1)})'
        
        REFERENCES:
    
        For more information, see Proposition 2.3 of [Ran2024]_.
        """
        P = self.parallelElement()
        F = set()
        for Q in P:
            R = Q.difference({random.choice(list(Q))})
            F = F.union(R)
        A = F.union(self.coloop())
        return self.deletion(A)


    def varchenkoMatrix(self):
        r"""
        Return the Varchenko matrix of a conditional oriented matroid.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        .. MATH::
    
            `\mathrm{V}(\mathcal{L}) := \big(\mathrm{v}(U,\,T)\big)_{T,U \in \mathcal{T}}`
        
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: L.varchenkoMatrix()
            [       1       a2       b1    a0*a2    a2*b1]
            [      b2        1    b1*b2       a0       b1]
            [      a1    a1*a2        1 a0*a1*a2       a2]
            [   b0*b2       b0 b0*b1*b2        1    b0*b1]
            [   a1*b2       a1       b2    a0*a1        1]
        
        .. SEEALSO::
        
            :mod:`sage.geometry.hyperplane_arrangement.hyperplane`.
        """
        M = self.simplification().tope()
        return matrix([[v(X, Y) for Y in M] for X in M])


    def varchenkoDeterminant(self):
        r"""
        Return the Varchenko determinant of a conditional oriented matroid.
    
        INPUT:
    
        - ``L`` -- a conditional oriented matroid
    
        .. MATH::
    
            `\det \mathrm{V}(\mathcal{L}) = \prod_{X \in \mathcal{L} \setminus \mathcal{T}} \Big(1 - \prod_{e \in X^0} q_{e,-1} q_{e,1}\Big)^{\theta(X)}` where `\theta(X) = \frac{\#\big\{T \in \mathcal{T}\ \big|\ \mathrm{Max}\,\{Y \in \mathcal{L}\ |\ Y \prec T,\, Y_f = 0\} = \{X\}\big\}}{2}` and `f \in X^0`.
        
        EXAMPLES::
    
            sage: L = COM({(1, 1, 1, 1, 0), (1, 0, 1, 1, 0), (1, -1, 1, 1, 0), (1, -1, 0, 1, 0), (1, -1, 0, 0, 0), (1, -1, 1, 0, 0), (1, -1, -1, 1, 0), (1, -1, -1, -1, 0), (1, -1, 1, -1, 0), (1, -1, -1, 0, 0), (1, -1, 0, -1, 0)})
            sage: L.varchenkoDeterminant()
            -(a0*b0 - 1)*(a1*b1 - 1)^2*(a2*b2 - 1)^2
        
        REFERENCES:
    
        For more information on this function, see Theorem 4.36 of [Ran2024]_.
    
        For more information on Varchenko determinants, see the following references:
    
        - [AM2017]_
    
        - [Ran2022]_
    
        - [Var1993]_
        """
        def Weight(X):
            x=1
            for i in zero(X):
                x = x*a[i]*b[i]
            return x
        def iBoundary(L, i, X):
            S = set()
            for Y in L._vectorset.difference({X}):
                if prec(Y, X) and (Y[i] == 0):
                    S = S.union({Y})
            return System(S)
        def Theta(L, X):
            M = []
            i = random.choice(list(zero(X)))
            for Y in L.tope():
                if iBoundary(L, i, Y).ismax(X):
                    M.append(Y)
            return len(M)/2
        N = self.simplification()
        return prod([(1-Weight(X))^(Theta(N, X)) for X in N._vectorset.difference(N.tope())])


    def isZero(self):
        r"""
        Return whether `\mathcal{L}` possesses the zero condition.        
    
        INPUT:
    
        - ``L`` -- a sign system
        
        .. MATH::
        
            A conditional oriented matroid `(E,\,\mathcal{L})` possesses the zero condition if:
            (Z) the zero element `(0,\, \dots,\, 0)` belongs to `\mathcal{L}`.        
    
        EXAMPLES::
    
            sage: L = COM({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})
            sage: L.isZero()
            True
        """
        return (tuple(0 for i in range(len(random.choice(list(self._vectorset))))) in self._vectorset)
    


# 4 Oriented Matroids



r"""
An oriented matroid is a conditional oriented matroid possessing the zero condition.
"""



class OM(COM):
    def __init__(self, vectorset):
        COM.__init__(self, vectorset)
        if not self.isZero():
            raise ValueError(f"a conditional oriented matroid possessing the zero condition expected, but got {vectorset}")
        self._vectorset = vectorset


    def __str__(self):
        r"""
        Print the oriented matroid `\mathcal{L}`.
    
        INPUT:
    
        - ``L`` -- a oriented matroid
    
        EXAMPLES::
    
            sage: L = OM({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})
            sage: L.__str__()
            'OM({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})'
        """
        return f"OM({self._vectorset})"


    def aguiarmahajanSystem(L, a):
        r"""
        Return the solution of an Aguiar-Mahajan linear system.
    
        INPUT:
    
        - ``L`` -- an oriented matroid
        - ``o`` -- an initial value associated to the zero vector
        
        .. MATH::
        
            Let `(E,\, \mathcal{L})` be an oriented matroid. Assign a variable `x_X` to each element `X \in \mathcal{L}`. The Aguiar-Mahajan system for `(E,\,\mathcal{L})` is the linear equation system `\sum_{\substack{X \in \mathcal{L} \\ Y \circ X = Y}} x_X\,\mathrm{v}(X,\,Y) = 0` indexed by `Y \in \mathcal{L} \setminus (0,\dots,0)`. It has a unique solution which can be computed recursively with the formula `x_Y = \frac{-1}{1 - \mathrm{v}(Y,\,-Y) \, \mathrm{v}(-Y,\,Y)} \sum_{\substack{X \in \mathcal{L} \\ X \prec Y}} \big(x_X + (-1)^{\mathrm{drk}\,Y}x_{-X} \, \mathrm{v}(-Y,\,Y)\big` with `\mathrm{drk}\,Y := \mathrm{rank}\,\mathcal{L} - \mathrm{corank}\,Y`.
    
        EXAMPLES::
    
            sage: L = OM({(0, 0, 0, 0, 0), (0, 0, -1, -1, 0), (0, 1, -1, -1, 0), (0, 1, 0, -1, 0), (0, 1, 1, -1, 0), (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, -1, 1, 1, 0), (0, -1, 0, 1, 0), (0, -1, -1, 1, 0), (0, -1, -1, 0, 0), (0, -1, -1, -1, 0)})
            sage: L.aguiarmahajanSystem(1)
            (0, -1, -1)  -->  -(b1*b2 - 1)/(a1*a2*b1*b2 - 1)
            (-1, 0, 1)  -->  -(a2*b0 - 1)/(a0*a2*b0*b2 - 1)
            (1, 0, -1)  -->  -(a0*b2 - 1)/(a0*a2*b0*b2 - 1)
            (1, 1, 0)  -->  -(a0*a1 - 1)/(a0*a1*b0*b1 - 1)
            (-1, 1, 1)  -->  -((a0*b2 - 1)*a1*a2*b0/(a0*a2*b0*b2 - 1) + (b1*b2 - 1)*a1*a2*b0/(a1*a2*b1*b2 - 1) - a1*a2*b0 + (a1*a2 - 1)/(a1*a2*b1*b2 - 1) + (a2*b0 - 1)/(a0*a2*b0*b2 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (-1, -1, -1)  -->  -((a0*a1 - 1)*b0*b1*b2/(a0*a1*b0*b1 - 1) + (a1*a2 - 1)*b0*b1*b2/(a1*a2*b1*b2 - 1) - b0*b1*b2 + (b0*b1 - 1)/(a0*a1*b0*b1 - 1) + (b1*b2 - 1)/(a1*a2*b1*b2 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (0, 0, 0)  -->  1
            (-1, -1, 1)  -->  -((a0*a1 - 1)*a2*b0*b1/(a0*a1*b0*b1 - 1) + (a0*b2 - 1)*a2*b0*b1/(a0*a2*b0*b2 - 1) - a2*b0*b1 + (a2*b0 - 1)/(a0*a2*b0*b2 - 1) + (b0*b1 - 1)/(a0*a1*b0*b1 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (1, -1, -1)  -->  -((a1*a2 - 1)*a0*b1*b2/(a1*a2*b1*b2 - 1) + (a2*b0 - 1)*a0*b1*b2/(a0*a2*b0*b2 - 1) - a0*b1*b2 + (a0*b2 - 1)/(a0*a2*b0*b2 - 1) + (b1*b2 - 1)/(a1*a2*b1*b2 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (1, 1, -1)  -->  -((a2*b0 - 1)*a0*a1*b2/(a0*a2*b0*b2 - 1) + (b0*b1 - 1)*a0*a1*b2/(a0*a1*b0*b1 - 1) - a0*a1*b2 + (a0*a1 - 1)/(a0*a1*b0*b1 - 1) + (a0*b2 - 1)/(a0*a2*b0*b2 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (-1, -1, 0)  -->  -(b0*b1 - 1)/(a0*a1*b0*b1 - 1)
            (1, 1, 1)  -->  -((b0*b1 - 1)*a0*a1*a2/(a0*a1*b0*b1 - 1) + (b1*b2 - 1)*a0*a1*a2/(a1*a2*b1*b2 - 1) - a0*a1*a2 + (a0*a1 - 1)/(a0*a1*b0*b1 - 1) + (a1*a2 - 1)/(a1*a2*b1*b2 - 1) - 1)/(a0*a1*a2*b0*b1*b2 - 1)
            (0, 1, 1)  -->  -(a1*a2 - 1)/(a1*a2*b1*b2 - 1)
        
        REFERENCES:
    
        For more information on this function, see Theorem 4.44 of [Ran2024]_.
    
        For more information on Aguiar-Mahajan systems, see the following references:
    
        - [AM2017]_
    
        - [Ran2022]_
        """
        def min_system(L):
            X = random.choice(list(L))
            for Y in L:
                if prec(Y, X):
                    X = Y
            return X
        def crk(L, X):
            k = 0
            F = System(L).face(X)._vectorset.difference({X})
            while not (F == set()):
                k = k+1
                Y = min_system(F)
                F = System(L).face(Y)._vectorset.difference({Y})
            return k
        def rk(L):
            k=0
            for X in L:
                k = max(k, crk(L, X))
            return k
        def drk(L, X):
            return rk(L) - crk(L, X)
        def Inf(L, X):
            S = set()
            for Y in L.difference({X}):
                if prec(Y, X):
                    S = S.union({Y})
            return S
        def am(L, X, a):
            S = Inf(L, X)
            if X == min_system(L):
                return a
            else:
                return (-1/(1-v(X, neg(X))*v(neg(X), X))) * sum(am(L, Y, a)+
                (-1)^(drk(L, X))*v(neg(X), X)*am(L, neg(Y), a) for Y in S)
        M = L.simplification()._vectorset
        for X in M:
            print (X, " --> ", am(M, X, a))
