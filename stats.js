var PI = Math.PI,
	SQRT2 = Math.SQRT2,
	ln = Math.log,
	e = Math.exp,
	pow = Math.pow,
	sqrt = Math.sqrt,
	sin = Math.sin,
	cos = Math.cos;
	
gamma = function (z) {
	// Computes the Gamma function to 10 decimal places using the Lanczos approximation for positive complex numbers here:
	// http://www.rskey.org/CMS/index.php/the-library/11
	
	// Use reflection formula for small and negative numbers: G(z)G(1 - z) = pi/sin(pi z)
	if (z < 0.5) {
		if (Number.isInteger(z))
			return NaN;
		
		/*
		G(z) = PI / [sin(z PI) G(1 - z)] 
		*/
		return PI / Math.sin(PI * z) / gamma(1 - z);
	}
	
	var q = [75122.6331530, 80916.6278952, 36308.2951477, 8687.24529705, 1168.92649479, 83.8676043424, 2.50662827511]
	var s = 0, p = 1;
	for (var n = q.length - 1; n >= 0; n--) {
		s = q[n] + z * s;
		p *= z + n
	}
	
	return s / p * Math.pow(z + 5.5, z + .5) * e(-z - 5.5);
}

gammaln = function (z) {
	if (z < 10)
		return ln(gamma(z));
	return z * ln(z) - z - ln(z / 2 / PI) / 2 + [12, -360, 1260, -1680, 1188].reduceRight((p, c) => 1/c/z + p/z/z, 0);
}

erf = function (x) {
	if (x < 0)
		return -erf(-x)
	
	var p = [-1.26551223, 1.00002368, 0.37409196, 0.09678418, -0.18628806, 0.27886807, -1.13520398, 1.48851587, -0.82215223, 0.17087277];
	var s = 0, t = 1 / (1 + x / 2);
	for (var n = p.length - 1; n >= 0; n--) {		
		s = p[n] + t * s;
	}
	
	return 1 - t * e(-x*x + s);
}

normalCDF = x => (1 + erf(x / Math.SQRT2)) / 2;

normalInvCDF = function (p) {
	var precision = Math.pow(10, -7),
		fn = x => normalCDF(x) - p
	
	// Initial guess
	var x = 0,
		y = fn(x);
	
	for (n = 0; n < 100 && Math.abs(y) > precision; n++) {
		x -= y * sqrt(2 * PI) * e(x*x / 2);
		y = fn(x);
	}
	
	return x;
}

beta = function (a, b) {
	return e(gammaln(a) + gammaln(b) - gammaln(a + b));
}

betaIncomplete = function (x, a, b) {
	return e(a * ln(x) + b * ln(1 - x))/ a * hypergeom(a + b, 1, a + 1, x, 10)
}

betaRegInc = function (x, a, b) {
	if (x > 0.5)
		return 1 - betaRegInc(1 - x, b, a);

	return betaIncomplete(x, a, b) / beta(a, b);
}

hypergeom = function (a, b, c, z, relError = 10) {
	// digits is number of digits of precision in base 10
	var p = Math.pow(10, relError);
	for (var s = 0, t = 1, n = 0; Math.abs(s / t) < p; n++) {		
		s += t;
		t *= z * (a + n) / (c + n) * (b + n) / (n + 1);
	}
	
	return s;
}

/*
	From http://www.real-statistics.com/students-t-distribution/noncentral-t-distribution/
	The CDF of the non-central t distribution is given as:
	F(t, k, d) = Phi(-d) + exp(-d^2 / 2) / 2 * Sigma[n = 0...inf] (d^2/2)^n * (I(r, m+1/2, k/2)/n! + d/(sqrt(2) * gamma(n + 3/2))*I(r, m+1, k/2))
	where Phi(x) is the CDF of the standard normal distribution and I is the CDF of the Beta distribution
	and r = t^2/(t^2 + k)
	
	Rearranging terms to aid in computation, the CDF becomes
	F(t, k, d) = Phi(-d) + 1/2 Sigma[n=0...inf] exp(n*ln(d^2/2) - d^2/2) (An + Cn)
	where An = 
*/
function nonCentralT_CDF (t, k, d, errorMag = 10) {
	var precision = Math.pow(10, errorMag);
	var r = t*t/(t*t + k);
	var d2o2 = d * d / 2;
	
	// Set initial values of terms to A_0, B_0, C_0, D_0
	var An = betaRegInc(r, .5, k / 2);
	var Bn = sqrt(Math.pow(1 - r, k) / PI / r) * e(gammaln((k - 1) / 2) - gammaln(k / 2));
	var Cn = d * sqrt(2 / PI) * (1 - Math.pow(1 - r, k / 2));
	var Dn = d * sqrt(2 / PI * Math.pow(1 - r, k));
	
	for (n = 0, s = 0, term = 1; Math.abs(s / term) < precision; n++) {
		var term = e(ln(An + Cn) - d2o2);
		s += term;

		// Set the terms for the next summation
		Bn *= d2o2 * r * (n + (k - 1) / 2) / (n + 1) / (n + .5); 
		Dn *= d2o2 * r * (n + k / 2) / (n + 1.5) / (n + 1);
		An = d2o2 * An / (n + 1) - Bn;
		Cn = d2o2 * Cn / (n + 1.5) - Dn;
	}
	
	return (1 + erf(-d / Math.SQRT2)) / 2 + s / 2;
}

function invNCTCDF (y, k, d, relError = 7) {
	var fn = t => nonCentralT_CDF(t, k, d) - y;
	var p = Math.pow(10, -relError);
	
	// Initial guess
	var x1 = d,
		x2 = d + 1/k,
		y1 = fn(x1),
		y2 = fn(x2);

	while (Math.abs(1 - x1/x2) > p) {
		var xn = x1 - y1 * (x1 - x2) / (y1 - y2);
		x2 = x1;
		y2 = y1;
		x1 = xn;
		y1 = fn(x1);
	}
	
	return x1;
} 

kParam = function (n, p, y) {
	// From http://www.itl.nist.gov/div898/handbook/prc/section2/prc263.htm
	// n is number of samples
	// p is the percentage of samples that fall above the bound
	// y is the confidence level
	return invNCTCDF(y, n - 1, normalInvCDF(p) * sqrt(n)) / sqrt(n);
}
