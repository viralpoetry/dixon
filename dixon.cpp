
/*

601528397      = 33461×17977      (0m4.568s)
3739492129     = 16769023x223     (0m2.608s)
35017839947    = 33461x1046527    (0m7.233s)
20639408833    = 139969×147457    (0m6.435s)
549567610591   = 1048391x524201   (1m2.132s) [39 bits]
821388891409   = 614657x1336337   (3m9.523s) [~40 bits]
5983391455009  = 1336337x4477457  (43 bits)
17549235333121 = 16769023x1046527 (44 bits)


Dixon, J. D. (1981). "Asymptotically fast factorization of integers"
http://www.ams.org/journals/mcom/1981-36-153/S0025-5718-1981-0595059-1/S0025-5718-1981-0595059-1.pdf

*/

#include <cstdio>

#include <NTL/ZZ.h>
#include <NTL/vec_ZZ.h>
#include <NTL/mat_ZZ.h>
#include <NTL/GF2.h>
#include <NTL/vec_GF2.h>
#include <NTL/mat_GF2.h>

NTL_CLIENT

int makeExponentVec(vec_GF2& Ai_GF2, vec_ZZ& Ai, const ZZ& a, const vec_ZZ& B) {
	ZZ q, z;

	z = q = a;
	clear(Ai_GF2);
	clear(Ai);

	for (int i=0 ; i<B.length() ; i++) {
		while (1) {
            if (!divide(q, z, B[i])) {
                break;
            }
			Ai_GF2[i]++;
			Ai[i]++;
			z = q;
		}
	}

    if (!IsOne(q)) {
        return 0;
    }
	return 1;
}

int findLinearCombination(int& minRate, vec_GF2& Xi, const mat_GF2& A) {
	mat_GF2 X;
	int index=0;

	// find the base matrix X of matrix A
	kernel(X, A);
	Xi.SetLength(X.NumCols());

	// 'rates' items are hamming weights of rows of matrix X
	int* rates;
	rates = new int[X.NumRows()];
	for (int i=0 ; i<X.NumRows() ; i++) {
		rates[i] = 0;
	}

	// rate the bases (rows) of matrix X
	for (int i=0 ; i<X.NumRows() ; i++) {
		for (int j=0 ; j<X.NumCols() ; j++) {
			if (IsOne(X.get(i,j))) rates[i]++;
		}
	}

	//find the row with the lowest rate (hamming weight)
	minRate = X.NumCols();
	for (int i=0 ; i<X.NumRows() ; i++) {
		if (rates[i] < minRate) {
			minRate = rates[i];
			index = i;
		}
	}
	for (int j=0 ; j<X.NumCols() ; j++) {
		Xi.put(j, X.get(index,j));
	}

	delete[] rates;
	rates = NULL;
	return 1;
}

// compute 'a' as conjuction of items of xRoots
int compute_a(ZZ& a, const vec_ZZ& xRoots, const ZZ& mod) {
	a = 1;
	for (int i=0 ; i<xRoots.length() ; i++) {
		a = MulMod(a, xRoots[i], mod);
	}
	return 1;
}

// compute 'b' as conjuction of primes from base with reduced exponents to one half
int compute_b(ZZ& b, const mat_ZZ& AiRoots, const vec_ZZ& B, const ZZ& mod) {
	vec_ZZ exp;
	exp.SetLength(AiRoots.NumCols());

	ZZ tmp;

	for (int i=0 ; i<AiRoots.NumRows() ; i++) {
		for (int j=0 ; j<AiRoots.NumCols() ; j++) {
			exp[j] += AiRoots[i][j];
		}
	}
	for (int j=0 ; j<exp.length() ; j++) {
		tmp = exp[j];
		if (!divide(exp[j], tmp, 2)) return 0;
	}

	b = 1;
	for (int i=0 ; i<exp.length() ; i++) {
		exp[i] = PowerMod(B[i], exp[i], mod);
		b = MulMod(b, exp[i], mod);
	}
	return 1;
}

// step 5 in Dixon's paper
int findFactor(ZZ& p, const ZZ& a, const ZZ& b, const ZZ& mod) {
    // if a != +-b
    if (!compare(a,b) || !compare(a,mod-b)) return 0;

	// compute factor as GCD(N,(a-b))
	GCD(p, mod, SubMod(a, b, mod));

	// if factor is trivial
	if (!compare(p,1) || !compare(p,mod)) return 0;

	return 1;
}

ZZ searchForBsmooth(int& square, ZZ& xfirst, mat_GF2& A_GF2, mat_ZZ& A, vec_ZZ& xCandidates,
                     ZZ& a, ZZ& b, const vec_ZZ& Base, const ZZ& N) {
    cout << "Search for B-smooth..." << endl;
	ZZ x = xfirst, x_2;
    ZZ rand;
    ZZ reminder;

	// vectors Ai_GF2 and Ai: factors of B-smooth integer (ZZ and GF2 versions)
	vec_GF2 Ai_GF2;
	Ai_GF2.SetLength(Base.length());
	vec_ZZ Ai;
	Ai.SetLength(Base.length());

    int k = Base.length();
    SetSeed(a + b + N);

    for (int i = 0; i <= k; ) {
        rand = RandomBnd(N-to_ZZ(1));
        ZZ reminder = GCD(rand, N);
        // return factor !
        if( reminder != to_ZZ(1)) {
            return reminder;
        }
        x_2 = PowerMod(rand, 2, N);

		// if there is a square number the funcion will directly set values 'a' and 'b' and return
		if (!compare(power(SqrRoot(x_2),2),x_2)) {
			a = xCandidates[0] = x;
			b = SqrRoot(x_2);
			square = 1;
            return to_ZZ(1);
		}

		// factor 'x' and make exponent vector (for base prime numbers)
		if (makeExponentVec(Ai_GF2, Ai, x_2, Base)) {
            xCandidates[i] = x;
            for (int j=0 ; j < Ai_GF2.length() ; j++) {
                A_GF2.put(k, j, Ai_GF2[j]);
                A[k][j] = Ai[j];
			}
            i++;
		}

        if (i > Ai.length()) {
            return to_ZZ(1);
		}
	}
    return to_ZZ(0);
}

int DixonFactorization(vec_ZZ& FactorsArray, mat_GF2& A_GF2, mat_ZZ& A, vec_GF2& Xi,
					   vec_ZZ& xCandidates, vec_ZZ& xRoots, mat_ZZ& AiRoots,
                       const vec_ZZ& Base, const ZZ& N) {
	ZZ xfirst, a, b, p, q;
	int square = 0, rootsCount;

	cout << "Integer to factorize: " << N << endl << endl;

	xfirst = SqrRoot(N-1)+1;
    cout << "Search for B-smooth integers and building matrices A, A_GF2" << endl;
	while (1) {
        ZZ res = searchForBsmooth(square, xfirst, A_GF2, A, xCandidates, a, b, Base, N);
        if(res != 1) {
            if (!divide(q, N, res)) {
                cerr << "FATAL ERROR" << endl;
                exit(EXIT_FAILURE);
            }

            cout << "Factors found: " << res << "  " << q << endl;
            append(FactorsArray, q);
            append(FactorsArray, res);
            return 1;
        }

        if (square == 0) {
			// find linear combination of matrix A
            cout << "Find the base matrix X of matrix A" << endl;
			findLinearCombination(rootsCount, Xi, A_GF2);

			// find x and Ai roots
			xRoots.SetLength(rootsCount);
			AiRoots.SetDims(rootsCount, Base.length());
			int k = 0;
			for (int i=0 ; i<Base.length()+1 ; i++) {
				if (IsOne(Xi[i])) {
					xRoots[k] = xCandidates[i];
					for (int j=0 ; j< AiRoots.NumCols() ; j++) {
						AiRoots[k][j] = A[i][j];
					}
					k++;
				}
			}

			// compute number 'a' from vector xRoots
            compute_a(a, xRoots, N);

			// compute number 'b' from vector AiRoots
			if (!compute_b(b, AiRoots, Base, N)) {
				cerr << "FATAL ERROR" << endl;
				exit(EXIT_FAILURE);
			}
		}

		// find factor 'p' of N
        if (findFactor(p, a, b, N)) {
			// compute factor 'q' as divide result N/p
			if (!divide(q, N, p)) {
				cerr << "FATAL ERROR" << endl;
				exit(EXIT_FAILURE);
			}

            cout << "Factors found: " << p << "  " <<q << endl;
            append(FactorsArray, q);
            break;
        }
		xfirst = xCandidates[0]+1;
	}
	return 1;
}

void generateBase(vec_ZZ& Base, const int baseLen, const ZZ& N) {
    int i = 0;
    PrimeSeq s;
    // -1 mod N
    //Base[0] = N - 1;

    while (i < baseLen) {
       Base[i] = s.next();
       i++;
    }
}

int main()
{
	ZZ N;

    cout << "Input integer N: ";
    cin >> N;
    //ZZ p, q;
    //GenPrime(p, 20, 80);
    //GenPrime(q, 20, 80);
    //mul(N, p, q);

    cout << "big O notation " << ceil(2.828427125*exp(sqrt(log(N)*log(log(N))))) << endl;

    cout << "Optimal size of the factor base for N = " << N << " : ";
    double baseLen = ceil(exp(sqrt(log(N)*log(log(N)))));
    cout << baseLen << endl;
    if(baseLen > 21000) {
        baseLen = 21000;
    }
    cout << "Used base: " << baseLen << endl;

	vec_ZZ Base;
	Base.SetLength(baseLen);

    generateBase(Base, baseLen, N);

	// matrix A: array of factor vectors of B-smooth integers (ZZ and GF2 versions)
    mat_ZZ A;
	mat_GF2 A_GF2;
    A.SetDims(baseLen+1,baseLen);
	A_GF2.SetDims(baseLen+1,baseLen);

	// vector Xi: indexes of rows of A_GF2 those makes linear combination
	vec_GF2 Xi;

	// vector xCandidates: candidates for roots for value a
	vec_ZZ xCandidates;
	xCandidates.SetLength(baseLen+1);

	// vector xRoots: roots (factors) for value a (a = x1*x2*...*xi)
	vec_ZZ xRoots;

	// matrix AiRoots: roots (factors) for value b
	mat_ZZ AiRoots;

	// vector FactorsArray: (prime) factors of N
	vec_ZZ FactorsArray;

	// do Dixon's factorization
    if (!DixonFactorization(FactorsArray, A_GF2, A, Xi, xCandidates, xRoots, AiRoots, Base, N)) {
		cout << "No factor found." << endl;
	}
	cout << "Factors of " << N << ": " << FactorsArray << endl;

	return EXIT_SUCCESS;
}
