@552
D = A

@SCREEN
D = D + A

@address
M = D

@i
M = 0

@k
M = 0

@l
M = 1

(LOOP_START)
	@128
	D = A  //definicija konstante
	
	@i
	D = M - D
	
	@LOOP_END
	D; JGE
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = 1 //stavi sve na jedinice i zacrni ga
	
	@i 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
	
	@LOOP_START
	0; JMP

(LOOP_END)


@j
M = 0


(LOOP_START2)
	@8
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END2
	D; JGE
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = -1 //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@1
	D = A
	
	@address 
	M = M + D
	
	@LOOP_START2
	0; JMP

(LOOP_END2)

@552
D = A

@SCREEN
D = D + A

@address
M = D


@j
M = 0


(LOOP_START3)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END3
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	
	
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START3
	0; JMP
	
	
(LOOP_END3)

@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START4)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END4
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START4
	0; JMP
	
	
(LOOP_END4)


@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START5)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END5
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START5
	0; JMP
	
	
(LOOP_END5)



@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START6)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END6
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START6
	0; JMP
	
	
(LOOP_END6)


@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START7)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END7
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START7
	0; JMP
	
	
(LOOP_END7)


@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START8)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END8
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START8
	0; JMP
	
	
(LOOP_END8)


@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START9)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END9
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START9
	0; JMP
	
	
(LOOP_END9)


@j
M = 0

@k
M = 0

@l
M = 1

@address
M = M + 1


(LOOP_START10)
	@16
	D = A  //definicija konstante
	
	@j
	D = M - D
	
	@LOOP_END10
	D; JGE
	
	
	@l
	D = M
	
	@k
	M = M + D 
	D = M
	
	@l
	M = D
	
	//zacrni registar screen + 32*i 
	@address
	A = M
	M = M | D //stavi sve na jedinice i zacrni ga
	
	@j 
	M = M + 1
	
	//povecaj adresu za 32
	@32
	D = A
	
	@address 
	M = M + D
		
	@LOOP_START10
	0; JMP
	
	
(LOOP_END10)

(END)
@END
0; JMP