sseg SEGMENT STACK
		byte 16384 DUP(?)
sseg ENDS

dseg SEGMENT PUBLIC
		byte 16384 DUP(?)
		sword ?
		byte 256 DUP(?)
		byte ? 
		sword 3
dseg ENDS

cseg SEGMENT PUBLIC
		ASSUME CS:cseg, DS:dseg

_strt:
		mov ax, dseg
		mov ds, ax
		mov cl, 255
		mov DS:[0], cl
		mov al, DS:[0]
		mov DS:[16642], al
		mov al, DS:[16642]
		mov DS:[0], al
R1:
		mov al, DS:[0]
		cmp al, 0
		je R2
dseg SEGMENT PUBLIC
		byte "Teste Compiladores$"
dseg ENDS
		mov si, 16645
		mov di, 0
R3:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R3
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
dseg SEGMENT PUBLIC
		byte "Escolha uma opcao:$"
dseg ENDS
		mov si, 16664
		mov di, 0
R4:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R4
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
dseg SEGMENT PUBLIC
		byte "1 Teste if $"
dseg ENDS
		mov si, 16683
		mov di, 0
R5:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R5
		mov dx, 0
		mov ah, 09h
		int 21h
dseg SEGMENT PUBLIC
		byte "2 Teste Atribuicao $"
dseg ENDS
		mov si, 16695
		mov di, 0
R6:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R6
		mov dx, 0
		mov ah, 09h
		int 21h
dseg SEGMENT PUBLIC
		byte "3 Termina$"
dseg ENDS
		mov si, 16715
		mov di, 0
R7:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R7
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
		mov dx, 256
		mov al, 255
		mov DS:[256], al
		mov ah, 0Ah
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
		mov di, 258
		mov ax, 0
		mov cx, 10
		mov dx, 1
		mov bh, 0
		mov bl, DS:[di]
		cmp bx, 2Dh
		jne R8
		mov dx, -1
		add di, 1
		mov bl, DS:[di]
R8:
		push dx
		mov dx, 0
R9:
		cmp bx, 0Dh
		je R10
		imul cx
		add bx, -48
		add ax, bx
		add di, 1
		mov bh, 0
		mov bl, DS:[di]
		jmp R9
R10:
		pop cx
		imul cx
		mov DS:[16384], ax
		mov ax, DS:[16384]
		mov DS:[0], ax
		mov cx, 1
		mov DS:[2], cx
		mov ax, DS:[0]
		mov bx, DS:[2]
		cmp ax, bx
		je R11
		mov al, 0
		jmp R12
R11:
		mov al, 255
R12:
		mov DS:[4], al
		mov al, DS:[4]
		cmp al, 255
		jne R13
dseg SEGMENT PUBLIC
		byte "IF Ok$"
dseg ENDS
		mov si, 16725
		mov di, 0
R15:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R15
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
		jmp R14
R13:
		mov ax, DS:[16384]
		mov DS:[0], ax
		mov cx, 2
		mov DS:[2], cx
		mov ax, DS:[0]
		mov bx, DS:[2]
		cmp ax, bx
		je R16
		mov al, 0
		jmp R17
R16:
		mov al, 255
R17:
		mov DS:[4], al
		mov al, DS:[4]
		cmp al, 255
		jne R18
dseg SEGMENT PUBLIC
		byte "Atribuicao OK$"
dseg ENDS
		mov si, 16731
		mov di, 0
R20:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R20
		mov si,16386
		mov di,0
R21:
		mov al, DS:[di]
		mov DS:[si], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R21
		mov si, 16386
		mov di, 0
R22:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R22
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
		jmp R19
R18:
		mov ax, DS:[16384]
		mov DS:[0], ax
		mov cx, 3
		mov DS:[2], cx
		mov ax, DS:[0]
		mov bx, DS:[2]
		cmp ax, bx
		je R23
		mov al, 0
		jmp R24
R23:
		mov al, 255
R24:
		mov DS:[4], al
		mov al, DS:[4]
		cmp al, 255
		jne R25
		mov cl, 0
		mov DS:[0], cl
		mov al, DS:[0]
		mov DS:[16642], al
		jmp R26
R25:
dseg SEGMENT PUBLIC
		byte "Opcao invalida$"
dseg ENDS
		mov si, 16745
		mov di, 0
R27:
		mov al, DS:[si]
		mov DS:[di], al
		add di, 1
		add si, 1
		cmp al, 24h
		jne R27
		mov dx, 0
		mov ah, 09h
		int 21h
		mov ah, 02h
		mov dl, 0Dh
		int 21h
		mov dl, 0Ah
		int 21h
R26:
R19:
R14:
		mov al, DS:[16642]
		mov DS:[0], al
		jmp R1
R2:
		mov ah, 4Ch
		int 21h
cseg ENDS
END _strt