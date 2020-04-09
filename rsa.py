
###############################################
####  SIMPLE RSA ALGORITHM IMPLEMENTATION  ####
####                +                      ####
####          CBC ENCRYPTION               ####
####              v1.0                     ####
####                                       ####
####                                       ####
####    by:  T.C.S.   01/2013              ####
####                                       ####
####                                       ####
####  functions:                           ####
####      generateKeys()                   ####
####      encrypt()                        ####
####      decrypt()                        ####
####                                       ####
####                                       ####
###############################################

#!/usr/bin/python

from random import randrange, getrandbits



###############################################
#######      AUXILIARY FUNCTIONS       ########
###############################################


def gcd(a,b):
  '''	euclidian algorithm
		
		example:		 
			gcd(143,559)	# 13		
	'''	
	while b != 0:
		a, b = b, a % b
	return a


def powmod(x,a,m):
	''' power module '''
	r = 1
	while a > 0:
		if a % 2 == 1: r = (r*x) % m
		a = a >> 1
		x = (x*x) % m
	return r



def extendedEuclids(d, f):
	''' extended gcd euclid's algorithm

		@param d: int
		@param f: int
		@returns: The tuple (x, y, gcd(d, f))
        where x and y satisfy the equation dx + fy = gcd(d, f)	
        
        example:
			extendedEuclids(143,559)	# (4, -1, 13)
	'''
	x = 0
	lastx = 1
	y = 1
	lasty = 0
	
	while f != 0:
		quotient = d / f
		(d, f) = (f, d % f)
		(x, lastx) = (lastx - quotient * x, x)
		(y, lasty) = (lasty - quotient * y, y)
	return (lastx, lasty, d)



def bitSize(number):
	'''Returns the number of bits required to hold a specific long number
		
		ex:
			bitSize(1024)	# 11
	'''

	if number < 0:
		raise ValueError('invalid number - only positives are allowed: %s' % number)
	
	if number == 0:
		return 1
	
	bits = 0
	while number:
		bits += 1
		number >>= 1
	
	return bits


def isPrime(n, k=5):
	'''
        Miller-Rabin primality test
        
        @param n: number to be testes
		@param k: number of tests/witnesses/confidence
		
		@returns: true if n is likely to be prime (higher k => higher 
					the probability), else false (composite)
		
		ex:
			isPrime(2)			# true
			isPrime(20)			# false
			isPrime(296354487)	# true                
        
	'''

	# special cases
	if n < 0: 
		return False
	if n == 2:
		return True
	if n % 2 == 0:	# not (n & 1)
		return False
	if n <= 1:
		return False
	if n <= 7:
		return True

	neg_one = n - 1

	s, d = 0, neg_one
	while not d & 1:		# while not even
		s, d = s+1, d>>1
	assert 2 ** s * d == neg_one and d & 1

	# tests
	for i in xrange(k):
		a = randrange(2, neg_one)
		x = pow(a, d, n)
		if x in (1, neg_one):
			continue
		for r in xrange(1, s):
			x = x ** 2 % n
			if x == 1:
				return False
			if x == neg_one:
				break
		else:
			return False
	return True



def getPrime(N = 512):
	'''
		generates a random prime with at least N bits
	'''
	p = getrandbits(N)
	while not isPrime(p):
		p = getrandbits(N)
	return p


def inverseModule(a, m):
	''' inverse of a module, i.e., determines b such that:
			b = 1/a mod m	
	
	arguments: the inverse of what we want and the module
	
	remarks: uses the extended euclides algorithm
	
		example:
			inverseModule(31,105)	# result: 61
	'''
	
	x, y, g = extendedEuclids(a, m)
	if g != 1:
		return None
	else:
		return x % m


def formatListOfBins(_list, nbits):
	'''
		pads a list of binaries with zeros (if necessary) to make it 
		size nbits		
	'''
	if len(_list) == 0:	# special case
		_list.append(0)	
	while (len(_list) % nbits):	
		_list.append(0)

def int2ListOfBins(number, nbits = 0):
	'''
		returns a list with the nbits binary representation 
		of a decimal number
		if nbits = 0, no pad will else it will complete the list with 0
		
		example:
			int2ListOfBins(5,7) # [1, 0, 1, 0, 0, 0, 0]

	'''
	_list = [int(x) for x in list(bin(number)[2:])]
	_list.reverse()
	if (nbits != 0):
		formatListOfBins(_list, nbits)
	return _list

	
		
###############################################
#######          RSA FUNCTIONS         ########
###############################################


def generateKeys(s):	
	'''
		generates RSA public/private keys size s bits
		
		@param s: number of bits of the key
			
		@returns: list of 3 tupples:
					[fac, priv, pub] where
						fac = (p,q)
						priv = (n,d) # private key
						pub = (n,e)  # public key
						
		example:
					generateKeys(1024)
	
		@remarks:
			- n = p*q is forced to be s bits long
			- p and q are also forced to be s/2 bits long each, because 
			  of this condition it could take from a few ms up to a few 
			  secs (depending on the key length) to find the the 2 primes
	 
	'''
	
	# generate primes considering - bits(p*q) = s and p~q	
	p = getPrime(s/2)
	while bitSize(p * p) != s:
		p = getPrime(s/2)
	print "first founded"
	q = p
	done = False
	while not done:
		q = getPrime(s/2)
		if bitSize(p * q) == s and p != q:
			done = True
	print "second founded"
		
	n = p * q
	m = (p - 1) * (q - 1)	# phi (totient)
	
	# exponential
	e = long(13)
	while e < m:
		if gcd(e, m) == 1: # check why when 11 and << bits => rsa error?
			break
		else:
			e = e + 1
			
	x, y, dd = extendedEuclids(m, e)
	if y > 0:
		d = y
	else:
		d = y % m

	fac = (p,q)
	priv = (n,d)
	pub = (n,e) 
	return (fac, priv, pub)





def encrypt(s,n,e,l):
	'''
		cbc block encryption using the rsa algorithm
		
		@param s: block size in bits
		@param n: rsa public key (pq)
		@param e: exponent - part of the public key
		@param l: boolean list to be encrypted
		
		@returns a boolean list, resulted from encrypting l. the first
				s bits is the randomly generated initialization vector
				
		@remarks:
			- if the size of l is not a multiple of s, its content will 
			  be extentend with 0 (false) in order to achieve this requirement
			- since in python: True = 1 and False = 0 => both notations 
			  can be use			  
			- the boolean list is ordered from lsb to msb, from left to 
			  right, i.e., [1,1,1,1,0,0,0,0,0,0] = 0000001111b = 15d
		
	'''
	
	# make sure s is multiple of l
	formatListOfBins(l,s)
	
	# size of the public key - after encryption each block
	# will be the same size as the key
	size = bitSize(n)
	
	# randomly generate a initialization with the same size as the block
	init_vector = int2ListOfBins(randrange((2**s)-1),s)

	# first size bits are the initialization vector
	result = init_vector
	cbc = sum(b<<i for i, b in enumerate(init_vector))
	
	while l:
		# get the decimal representation of the binary in the block
		block = sum(b<<i for i, b in enumerate(l[:s]))

		# remove current block from list
		# !!!it would be more efficient to use a moving index?
		l = l[s:]
				
		# encrypt
		block = block ^ cbc			# xor
		block = (block ** e) % n	# rsa
		cbc = block					# save ciphertext for the next iteration

		# decimal to binary in list format and add it to the output list
		result += int2ListOfBins(block,size)
	
	return result
		





def decrypt(s, n , d, l):
	'''
		cbc block decryption using the rsa algorithm
		
		@param s: block size in bits
		@param n: part of the private key (pq)
		@param d: other part of the public key
		@param l: boolean list to be decrypted, where the first s bits are
				  the initalization list
		
		@returns a the decrypted list without the initalization vector		
		
		@notes:
			- l size must be a multiple of s
	'''
	
	init_vector = l[:s]		# get the init vector
	
	cbc = sum(b<<i for i, b in enumerate(init_vector))

	l = l[s:] 		# remove init vector				

	# after encryption the size of each block is the same as the key size
	size = bitSize(n)
	result = []
	while l:
		# get the decimal representation of the block
		block = sum(b<<i for i, b in enumerate(l[:size])) 

		# remove current block from list
		# !!!it would be more efficient to use a moving index!!!
		l = l[size:]
	
		# decrypt
		temp = block				# save current ciphertext for the next iteration
		block = powmod(block,d,n)	# rsa
		block = block ^ cbc			# xor
		cbc = temp

		# decimal to binary in list format and add it to the output list
		result += int2ListOfBins(block,s)

	return result
	




################### TESTS #####################
## ATTENTION:                                ##                        
##        THIS PART USES THE TIME MODULE     ##
###############################################


import time

def testA(nbits, nrandomtests):
	a = generateKeys(nbits)
	print "\n\nkey size requested > ", nbits
	print "\np > ", a[0][0]
	print "q > ", a[0][1]
	print "n > ", a[1][0]
	print "d > ", a[1][1]
	print "e > ", a[2][1]
	print "\nsize of n=pq > ",bitSize (a[1][0])

	print "\n\ntesting enc/dec random messages with generated keys ..."
	for i in range(nrandomtests):
		msg = int (getrandbits(nbits-1))
		crypted = (msg ** a[2][1]) % a[1][0]
		original = powmod(crypted,a[1][1],a[1][0])
		if msg == original:
			print "test " + str(i) + " OK"
		else:
			print "test " + str(i) + " FAIL"



def testB(keysize, list_size, block_size):
	print "\n\n----------- TEST CASE ------------------"
	print "key size > ", keysize
	print "bits to encrypt/decrypt > ", list_size
	print "block size > ", block_size
	testlist = int2ListOfBins(int(getrandbits(list_size-1)),list_size)	
	print "generating keys ... ",
	t = time.time()
	a = generateKeys(keysize)
	print "done in %0.4f s" % (time.time() - t)
	print "encrypting list ... ",
	t = time.time()
	criptedlist = encrypt(block_size,a[1][0],a[2][1],testlist)
	print "done in %0.4f s" % (time.time() - t)
	print "decrypting list ... ",
	t = time.time()
	decriptedlist = decrypt(block_size,a[1][0],a[1][1],criptedlist)
	print "done in %0.4f s" % (time.time() - t)
	# remove the last 5 values in case they are all zeros in the
	# original list - the prob. of all 5 be zeros ~ 1/2^5
	if testlist[:keysize-5] == decriptedlist[:keysize-5]:
		print "\t** SUCCESS **"
	else:
		print "\t** FAIL **"
	print "---------------------------"


testB(200,3000,150)
#testB(64,1000,32)
#testB(64,1000,50)
#testB(512,10000,64)
#testB(512,10000,511)
#testB(1024,10000,256)
#testB(1024,10000,512)
#testB(1024,10000,1023)
#testB(4096,10000,1023)

