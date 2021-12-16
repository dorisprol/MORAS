@1
D = M 
@e
M = D

@EKSP_VECI_OD_0
D;JGT


@2
M=1
@END
0;JMP


(EKSP_VECI_OD_0)
@0
D = M 
@i
M = D 
@2
M = D 
@j
M = D 

(LOOP1_START)
	@e
	D = M
	@LOOP1_END
	D-1;JEQ
	(LOOP2_START)
		@i
		D = M
		
		@LOOP2_END
		D-1;JEQ

		@j
		D = M
		@2
		M = M + D
		@i
		M = M - 1
		
		@LOOP2_START
		0;JMP

	(LOOP2_END)
	@2
	D = M
	@j
	M = D
	@0
	D = M
	@i
	M = D
	@e
	M = M-1

	@LOOP1_START
	0;JMP
(LOOP1_END)

(END)
@END
0;JMP