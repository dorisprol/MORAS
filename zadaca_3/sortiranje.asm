(LOOP1_START)
	@0
	D = M

	@LOOP1_END
	D; JEQ

	@100
	D = D-1
	D = A + D
	A = D
	D = M

	@i
	M = D
	@0
	D = M
	@1
	M = D-1
	@i
	D = M

	@a
	M = D
	@0
	D = M
	@max
	M = D
	
	(LOOP2_START)
		@1
		D = M
	
		@LOOP2_END
		D; JEQ
	
		@100
		D = D-1
		D = A + D
		A = D
		D = M
	
		@n
		M = D 
		@a
		D = M-D
	
		@OZN
		D; JGT
	
		@n
		D = M
		@a
		M = D
		
		@1
		D = M
		@max
		M = D
		
		(OZN)
		@1
		M=M-1
		
		@LOOP2_START
		0;JMP
	(LOOP2_END)
	
	@0
	D = M
	@100
	D = A
	@0
	D = D+M
	@temp
	M = D-1

	@a
	D = M

	@temp
	A = M
	M = D

	@100
	D = A

	@max
	D = D+M

	@temp
	M = D-1

	@i
	D = M
	@temp
	A = M
	M = D
	
	@0
	M = M-1

	@LOOP1_START
	0;JMP
(LOOP1_END)

(END)
@END
0;JMP