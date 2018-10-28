/*
	Membros do grupo:
	Herbert Alves Batista
	Luiz Gustavo Avelino Mendes
	Thiago Henrique Balbino Dias
*/

//----------------------------------
// BIBLIOTECAS
//----------------------------------


#include <stdio.h>
#include <iostream>
#include <string>
#include "SintAnalyzer.h"
#include "SymbTab.h"
#include "RegLexico.h"
#include "LexAnalyzer.h"
#include <fstream>
#include <sstream>
using namespace std;

/**
*   Construtor
*/
SintAnalyzer::SintAnalyzer(){
registroLexico;

}


/**
*   Destrutor
*/
SintAnalyzer::~SintAnalyzer(){
}


void SintAnalyzer::teste(){
	cout << "\n\nteste ok\n\n";
}

/**
 *  Procedimento S
 */
void SintAnalyzer::S(){
    fileOut << "sseg SEGMENT STACK\n";
	fileOut << "\t\tbyte 16384 DUP(?)\n";
	fileOut << "sseg ENDS\n\n";

	fileOut << "dseg SEGMENT PUBLIC\n";
	fileOut << "\t\tbyte 16384 DUP(?)\n";
	
    if(currentToken != NULL){
            notNull = true;
        if(currentToken->cod == 'G' || currentToken->cod == '2'){
            while(notNull){
                if(currentToken->cod == 'G' || currentToken->cod == '2')
                    DECL();
                else
                    notNull = false;
                }
            }
    fileOut << "dseg ENDS\n\n";

	fileOut << "cseg SEGMENT PUBLIC\n";
	fileOut << "\t\tASSUME CS:cseg, DS:dseg\n\n";

	fileOut << "_strt:\n";
	fileOut << "\t\tmov ax, dseg\n";
	fileOut << "\t\tmov ds, ax\n";

        BLOCO();

    fileOut << "\t\tmov ah, 4Ch\n";
    fileOut << "\t\tint 21h\n";
    fileOut << "cseg ENDS\n";
    fileOut << "END _strt";
    //fileOut.flush();
    }

}

/**
 *  Procedimento DECL
 */
void SintAnalyzer::DECL(){
    if(currentToken != NULL){
            notNull = true;
        if(currentToken->cod == 'G'){
            match('G');
            LexRecord * id = currentToken;

            match('H');
            // Ação semantica
            if(id->adressTable->classe.compare("vazio")==0){
                id->adressTable->classe = "constante";
            } else {
                /**ERRO SEMANTICO**/
                cout << id->lineNumber << ":identificador ja declarado [" << id->lexema << "].";
            }
            match('1');
            SymbolNode * valor;

            VALOR(&valor);

            // Ação semantica
            id->adressTable->tipo = tabSimbNaoTerminais.search("VALOR")->tipo;
            match('K');

            // Geração de Codigo
            id->adressTable->end = dataCount;
            if(id->adressTable->tipo.compare("string")==0){

                fileOut << "\t\tbyte " << valor->lexema << "\n";
                updateDataCount(valor->lexema.length()-2);

            } else if(id->adressTable->tipo.compare("byte")==0){

                        fileOut << "\t\tbyte " << valor->lexema << "\n";
                        updateDataCount(1);

                    } else if(id->adressTable->tipo.compare("logico")==0){

                                if(valor->lexema.compare("TRUE")==0){
                                    fileOut << "\t\tbyte 255\n";
                                } else {
                                    fileOut << "\t\tbyte 0\n";
                                }
                                updateDataCount(1);

                                } else {
                                    fileOut << "\t\tsword " << valor->lexema << "\n";
                                    updateDataCount(2);
                                }

        } else {
            TIPO();

            LexRecord * id = currentToken;
            match('H');
            // Ação Semantica
            if(id->adressTable->classe.compare("vazio")==0){
                id->adressTable->classe = "variavel";
            } else {
                /**ERRO SEMANTICO**/
                cout << id->lineNumber << ":identificador ja declarado [" << id->lexema << "].";
            }
            //Ação Semantica
            id->adressTable->tipo = tabSimbNaoTerminais.search("TIPO")->tipo;

            if(notNull){
                if(currentToken->cod == '1'){
                    match('1');
                    SymbolNode * valor;
                    VALOR(&valor);
                    // Ação Semantica
                    if(id->adressTable->tipo != tabSimbNaoTerminais.search("VALOR")->tipo){
                       /**ERRO SEMANTICO**/
                       cout << id->lineNumber << ":tipos incompativeis.";
                    }

                    // Geração de Codigo
                    id->adressTable->end = dataCount;

                    if(id->adressTable->tipo.compare("string")==0){

                        fileOut << "\t\tbyte " << valor->lexema << "\n";
                        fileOut << "\t\tbyte " << 256 - valor->lexema.length() << " DUP(?)\n";
                        updateDataCount(256);

                    } else if(id->adressTable->tipo.compare("byte")==0){

                            fileOut << "\t\tbyte " << valor->lexema << "\n";
                            updateDataCount(1);

                        } else if(id->adressTable->tipo.compare("logico")==0){

                                    if(valor->lexema.compare("TRUE")==0){
                                        fileOut << "\t\tbyte 255\n";
                                    } else {
                                        fileOut << "\t\tbyte 0\n";
                                    }
                                    updateDataCount(1);

                                    } else {
                                        fileOut << "\t\tsword " << valor->lexema << "\n";
                                        updateDataCount(2);
                                    }
                } else {

                    // Geração de Codigo
                    id->adressTable->end = dataCount;

                    if(id->adressTable->tipo.compare("string")==0){

                        fileOut << "\t\tbyte 256 DUP(?)\n";
                        updateDataCount(256);

                    } else if(id->adressTable->tipo.compare("byte")==0 or id->adressTable->tipo.compare("logico")==0){

                                fileOut << "\t\tbyte ? \n";
                                updateDataCount(1);

                            } else {
                                fileOut << "\t\tsword ?\n";
                                updateDataCount(2);
                            }

                }
            }
            while(notNull){
                if(currentToken->cod == 'B'){
                    match('B');
                    id = currentToken;
                    match('H');
                    // Ação Semantica
                    if(id->adressTable->classe.compare("vazio")==0){
                        id->adressTable->classe = "variavel";
                    } else {
                        /**ERRO SEMANTICO**/
                        cout << id->lineNumber << ":identificador ja declarado [" << id->lexema << "].";
                    }
                    //Ação Semantica
                    id->adressTable->tipo = tabSimbNaoTerminais.search("TIPO")->tipo;

                    if(notNull){
                        if(currentToken->cod == '1'){
                            match('1');
                            SymbolNode * valor;
                            VALOR(&valor);

                             // Ação Semantica
                            if(id->adressTable->tipo != tabSimbNaoTerminais.search("VALOR")->tipo){
                                /**ERRO SEMANTICO**/
                                cout << id->lineNumber << ":tipos incompativeis.";
                            }

                            // Geração de Codigo
                            id->adressTable->end = dataCount;

                            if(id->adressTable->tipo.compare("string")==0){

                                fileOut << "\t\tbyte " << valor->lexema << "\n";
                                fileOut << "\t\tbyte " << 256 - valor->lexema.length() << " DUP(?)\n";
                                updateDataCount(256);

                            } else if(id->adressTable->tipo.compare("byte")==0){

                                    fileOut << "\t\tbyte " << valor->lexema << "\n";
                                    updateDataCount(1);

                                } else if(id->adressTable->tipo.compare("logico")==0){

                                            if(valor->lexema.compare("TRUE")==0){
                                                fileOut << "\t\tbyte 255\n";
                                            } else {
                                                fileOut << "\t\tbyte 0\n";
                                            }
                                            updateDataCount(1);

                                            } else {
                                                fileOut << "\t\tsword " << valor->lexema << "\n";
                                                updateDataCount(2);
                                            }
                        } else {

                            // Geração de Codigo
                            id->adressTable->end = dataCount;

                            if(id->adressTable->tipo.compare("string")==0){

                                fileOut << "\t\tbyte 256 DUP(?)\n";
                                updateDataCount(256);

                            } else if(id->adressTable->tipo.compare("byte")==0 or id->adressTable->tipo.compare("logico")==0){

                                        fileOut << "\t\tbyte ? \n";
                                        updateDataCount(1);

                                    } else {
                                        fileOut << "\t\tsword ?\n";
                                        updateDataCount(2);
                                    }

                        }
                    }
                } else notNull = false;
            }
            match('K');
        }
    }
}



/**
 *  Procedimento TIPO
 */
void SintAnalyzer::TIPO(){
    SymbolNode * tipo = tabSimbNaoTerminais.insert(0, "TIPO");
	// Ação Semantica
    if(currentToken->lexema.compare("integer")==0){
        tipo->tipo = "inteiro";
    } else if(currentToken->lexema.compare("byte")==0){
                tipo->tipo = "byte";
            } else if(currentToken->lexema.compare("boolean")==0){
                        tipo->tipo = "logico";
                    }else{
                        tipo->tipo = "string";
                    }
	match('2');
}

/**
 *  Procedimento VALOR
 */
void SintAnalyzer::VALOR(SymbolNode ** v2){
    if(currentToken != NULL){
        SymbolNode* valor = tabSimbNaoTerminais.insert('0', "VALOR");

        notNull = true;
        if(currentToken->lexema.compare("-") == 0){
            match('C');
            *v2 = currentToken->adressTable;
        } else {
            *v2 = currentToken->adressTable;
        }
        if(notNull){
            if(currentToken->cod == 'F'){
                valor->tipo = "inteiro";
                match('F');
            } else if(notNull){
                if(currentToken->cod == 'L'){
                    valor->tipo = "logico";
                    match('L');
                } else if(notNull){
                    if(currentToken->cod == 'M' || currentToken->cod == 'I'){
                        valor->tipo = "byte";
                        match('M');
                    } else {
                        valor->tipo = "string";
                        match('N');
                    }
                }
            }
        }
    }
}

/**
 *  Procedimento BLOCO
 */
void SintAnalyzer::BLOCO(){
	match('D');
	if(currentToken != NULL){
            notNull = true;
        if(currentToken->cod == 'H' || currentToken->cod == 'I' || currentToken->cod == '5' || currentToken->cod == '3' ||
            currentToken->cod == 'K' || currentToken->cod == '6' || currentToken->cod == '7'){

            while(notNull){
                if(currentToken->cod == 'H' || currentToken->cod == 'I' || currentToken->cod == '5' || currentToken->cod == '3' ||
                currentToken->cod == 'K' || currentToken->cod == '6' || currentToken->cod == '7'){
                    COMANDO();

                } else notNull = false;
            }
        }
	}
	match('E');
}

/**
 *  Procedimento COMANDO
 */
void SintAnalyzer::COMANDO(){

	if (currentToken->cod == 'H' || currentToken->cod == 'I') COMANDO_ATRIB();
	else if (currentToken->cod == '5') COMANDO_REPET();
	else if (currentToken->cod == '3') COMANDO_TESTE();
	else if (currentToken->cod == 'K') COMANDO_NULO();
	else if (currentToken->cod == '6') COMANDO_LEITURA();
	else if (currentToken->cod == '7') COMANDO_ESCRITA();
}

/**
 *  Procedimento COMANDO_ATRIB
 */
void SintAnalyzer::COMANDO_ATRIB(){
	LexRecord * id = currentToken;

	// Ação Semantica
    if(id->adressTable->classe.compare("vazio")==0){
        /**ERRO SEMANTICO**/
		cout << id->lineNumber << ":identificador nao declarado [" << id->lexema << "].";
    } else
        if(id->adressTable->classe.compare("variavel")!=0){
            /**ERRO SEMANTICO**/
            cout << id->lineNumber << ":classe de identificador incompatível [" << id->lexema << "].";
        }

	match('H');
	match('1');
	tempCount = 0;
	EXPRESSAO();

	// Ação Semantica
	if(id->adressTable->tipo != tabSimbNaoTerminais.search("EXPRESSAO")->tipo){
            if(id->adressTable->tipo.compare("inteiro")!=0 or tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")!=0){
                /**ERRO SEMANTICO**/
                cout << id->lineNumber << ":tipos incompatíveis. ";
            }



    }

	// Geração de Codigo

	if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")==0 or
	   tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("logico")==0){
		   fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
		   fileOut << "\t\tmov DS:[" << id->adressTable->end << "], al\n";

	   } else
		   if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("inteiro")==0){
				fileOut << "\t\tmov ax, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
				fileOut << "\t\tmov DS:[" << id->adressTable->end << "], ax\n";

			} else
				if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("string")==0){
					fileOut << "\t\tmov si," << id->adressTable->end << "\n";
					fileOut << "\t\tmov di," << tabSimbNaoTerminais.search("EXPRESSAO")->end << "\n";
					std::string rotInicio = getLabel();
					fileOut << rotInicio << ":\n";
					fileOut << "\t\tmov al, DS:[di]\n";
					fileOut << "\t\tmov DS:[si], al\n";
					fileOut << "\t\tadd di, 1\n";
					fileOut << "\t\tadd si, 1\n";
					fileOut << "\t\tcmp al, 24h\n";
					fileOut << "\t\tjne " << rotInicio << "\n";

				}

	match('K');
}

/**
 *  Procedimento COMANDO_REPET
 */
void SintAnalyzer::COMANDO_REPET(){

	match('5');
	tempCount = 0;
	LexRecord * expressao = currentToken;
	EXPRESSAO();
	// Ação Semantica
	if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("logico")!=0){
        /**ERRO SEMANTICO**/
		cout << expressao->lineNumber << ":tipos incompatíveis.";
    }
    if(currentToken != NULL){

        // Geração de codigo
        string rotInicio = getLabel();
        string rotFim = getLabel();
        fileOut << rotInicio << ":\n";
        fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
        fileOut << "\t\tcmp al, 0\n";
        fileOut << "\t\tje " << rotFim << "\n";

        if (currentToken->cod == 'D'){
            BLOCO();
        }else{
            COMANDO();
        }

         // Refazer a EXPRESSAO antes de colocar o salto
        LexRecord * pontoAtual = currentToken;
        registroLexico.nextToken = expressao;
        currentToken = registroLexico.getNextToken();
        tempCount = 0;
        EXPRESSAO();
        registroLexico.nextToken = pontoAtual;
        currentToken = registroLexico.getNextToken();
        notNull = true;
        fileOut << "\t\tjmp " << rotInicio << "\n";
        fileOut << rotFim << ":\n";

    }
}


/**
 *  Procedimento COMANDO_TESTE
 */
void SintAnalyzer::COMANDO_TESTE(){
	match('3');
	tempCount = 0;

	EXPRESSAO();

	// Ação Semantica
	if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("logico")!=0){
        /**ERRO SEMANTICO**/
		cout << currentToken->lineNumber << ":tipos incompatíveis.";
    }

	match('P');

	string rotFalso = getLabel();
	string rotFim = getLabel();

	if(currentToken != NULL){

        // Geração de codigo
        fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
        fileOut << "\t\tcmp al, 255\n";
        fileOut << "\t\tjne " << rotFalso << "\n";

        if (currentToken->cod == 'D'){
            BLOCO();
        }else{
            COMANDO();
        }

        fileOut << "\t\tjmp " << rotFim << "\n";

    }

    if(currentToken != NULL){

        fileOut << rotFalso << ":\n";

        if (currentToken->cod == '4'){
            match('4');

            if(currentToken != NULL){

                if (currentToken->cod == 'D'){
                    BLOCO();
                }else{
                    COMANDO();
                }

            }
        }
        fileOut << rotFim << ":\n";
    }
}


/**
 *  Procedimento COMANDO_NULO
 */
void SintAnalyzer::COMANDO_NULO(){
	match('K');
}


/**
 *  Procedimento COMANDO_LEITURA
 */
void SintAnalyzer::COMANDO_LEITURA(){
	match('6');
	match('B');

	// Ação Semantica
	if(currentToken->adressTable->classe.compare("vazio")!=0){
        if(currentToken->adressTable->tipo.compare("byte")!=0 and currentToken->adressTable->tipo.compare("inteiro")!=0 and currentToken->adressTable->tipo.compare("string")!=0){
            /**ERRO SEMANTICO**/
            cout << currentToken->lineNumber << ":tipos incompativeis";
        }
	}else{
	    /**ERRO SEMANTICO**/
        cout << currentToken->lineNumber << ":identificador nao declarado [" << currentToken->lexema << "].";
	}

	// Geração de codigo
	// interrupção para leitura do teclado
	int bufferEnd = tempCount;
	updateTempCount(2);
	fileOut << "\t\tmov dx, " << bufferEnd << "\n";
	fileOut << "\t\tmov al, 255\n";
	fileOut << "\t\tmov DS:[" << bufferEnd << "], al\n";
	fileOut << "\t\tmov ah, 0Ah\n";
	fileOut << "\t\tint 21h\n";

	// quebra de linha
	fileOut << "\t\tmov ah, 02h\n";
	fileOut << "\t\tmov dl, 0Dh\n";
	fileOut << "\t\tint 21h\n";
	fileOut << "\t\tmov dl, 0Ah\n";
	fileOut << "\t\tint 21h\n";

	if(currentToken->adressTable->tipo.compare("byte")==0 or currentToken->adressTable->tipo.compare("inteiro")==0){

        string rotNaoNegativo = getLabel();
		string rotInicio = getLabel();
		string rotFim = getLabel();

		fileOut << "\t\tmov di, " << bufferEnd+2 << "\n";
		fileOut << "\t\tmov ax, 0\n";
		fileOut << "\t\tmov cx, 10\n";
		fileOut << "\t\tmov dx, 1\n";
		fileOut << "\t\tmov bh, 0\n";
		fileOut << "\t\tmov bl, DS:[di]\n";
		fileOut << "\t\tcmp bx, 2Dh\n";
		fileOut << "\t\tjne " << rotNaoNegativo << "\n";
		fileOut << "\t\tmov dx, -1\n";
		fileOut << "\t\tadd di, 1\n";
		fileOut << "\t\tmov bl, DS:[di]\n";

		fileOut << rotNaoNegativo << ":\n";
		fileOut << "\t\tpush dx\n";
		fileOut << "\t\tmov dx, 0\n";

		fileOut << rotInicio << ":\n";
		fileOut << "\t\tcmp bx, 0Dh\n";
		fileOut << "\t\tje " << rotFim << "\n";
		fileOut << "\t\timul cx\n";
		fileOut << "\t\tadd bx, -48\n";
		fileOut << "\t\tadd ax, bx\n";
		fileOut << "\t\tadd di, 1\n";
		fileOut << "\t\tmov bh, 0\n";
		fileOut << "\t\tmov bl, DS:[di]\n";
		fileOut << "\t\tjmp " << rotInicio << "\n";

		fileOut << rotFim << ":\n";
		fileOut << "\t\tpop cx\n";
		fileOut << "\t\timul cx\n";

		if(currentToken->adressTable->tipo.compare("byte")==0){
            fileOut << "\t\tmov DS:[" << currentToken->adressTable->end << "], al\n";
		}else{
            fileOut << "\t\tmov DS:[" << currentToken->adressTable->end << "], ax\n";
		}
	}else
        if(currentToken->adressTable->tipo.compare("string")==0){

            string rotInicio = getLabel();
			string rotFim = getLabel();
			fileOut << "\t\tmov si, " << currentToken->adressTable->end << "\n";
			fileOut << "\t\tmov di, " << bufferEnd+2 << "\n";
			fileOut << rotInicio << ":\n";
			fileOut << "\t\tmov al, DS:[di]\n";
			fileOut << "\t\tcmp al, 0Dh\n";
			fileOut << "\t\tje " << rotFim << "\n";
			fileOut << "\t\tmov DS:[si], al\n";
			fileOut << "\t\tadd di, 1\n";
			fileOut << "\t\tadd si, 1\n";
			fileOut << "\t\tjmp " << rotInicio << "\n";
			fileOut << rotFim << ":\n";
			fileOut << "\t\tmov al, 24h\n";
			fileOut << "\t\tmov DS:[si], al\n";

        }

	match('H');
	match('K');
}

/**
 *  Procedimento COMANDO_ESCRITA
 */
void SintAnalyzer::COMANDO_ESCRITA(){

    bool quebraLinha = false;
    if(currentToken->adressTable->lexema.compare("writeln")==0){
        quebraLinha = true;
    }

	match('7');
	match('B');
	tempCount = 0;
	EXPRESSAO();

	// Ação Semantica
    if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")!=0 and
       tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("inteiro")!=0 and
       tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("string")!=0){

        /**ERRO SEMANTICO**/
        cout << currentToken->lineNumber << ":tipos incompativeis";

    }

	// Geração de codigo
	{

	    int stringTempEnd = tempCount;

	    if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")==0 or tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("inteiro")==0){

            if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")==0){
                fileOut << "\t\tmov ah, 0\n";
				fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
				updateTempCount(1);
            } else {
                fileOut << "\t\tmov ax, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
                updateTempCount(2);
            }


			string rotPositivo = getLabel();
			string rotLoop1 = getLabel();
			string rotLoop2 = getLabel();
			fileOut << "\t\tmov di, " << stringTempEnd << "\n";
			fileOut << "\t\tmov cx, 0\n";
			fileOut << "\t\tcmp ax, 0\n";
			fileOut << "\t\tjge " << rotPositivo << "\n";
			fileOut << "\t\tmov bl, 2Dh\n";
			fileOut << "\t\tadd di, 1\n";
			fileOut << "\t\tneg ax\n";
            fileOut << rotPositivo << ":\n";
			fileOut << "\t\tmov bx, 10\n";
            fileOut << rotLoop1 << ":\n";
			fileOut << "\t\tadd cx, 1\n";
			fileOut << "\t\tmov dx, 0\n";
			fileOut << "\t\tidiv bx\n";
			fileOut << "\t\tpush dx\n";
			fileOut << "\t\tcmp ax, 0\n";
			fileOut << "\t\tjne " << rotLoop1 << "\n";
            fileOut << rotLoop2 << ":\n";
			fileOut << "\t\tpop dx\n";
			fileOut << "\t\tadd dx, 48\n";
			fileOut << "\t\tmov ds:[di], dl\n";
			fileOut << "\t\tadd di, 1\n";
			fileOut << "\t\tadd cx, -1\n";
			fileOut << "\t\tcmp cx, 0\n";
			fileOut << "\t\tjne " << rotLoop2 << "\n";
			// grava o fim da string "$"
			fileOut << "\t\tmov dl, 24h\n";
			fileOut << "\t\tmov DS:[di], dl\n";

	    }else
            if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("string")==0){

                stringTempEnd = tabSimbNaoTerminais.search("EXPRESSAO")->end;

            }
        // mostra a string na tela
		fileOut << "\t\tmov dx, " << stringTempEnd << "\n";
		fileOut << "\t\tmov ah, 09h\n";
		fileOut << "\t\tint 21h\n";

	}

    if(currentToken != NULL){
            notNull = true;
      // if (currentToken->cod == 'B'){
            while(notNull){
                if(currentToken->cod == 'B'){

                    match('B');
                    tempCount = 0;
                    EXPRESSAO();

                    // Geração de codigo
                    {
                        int stringTempEnd = tempCount;

                        if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")==0 or tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("inteiro")==0){

                            if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("byte")==0){
                                fileOut << "\t\tmov ah, 0\n";
                                fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
                                updateTempCount(1);
                            } else {
                                fileOut << "\t\tmov ax, DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "]\n";
                                updateTempCount(2);
                            }


                            string rotPositivo = getLabel();
                            string rotLoop1 = getLabel();
                            string rotLoop2 = getLabel();
                            fileOut << "\t\tmov di, " << stringTempEnd << "\n";
                            fileOut << "\t\tmov cx, 0\n";
                            fileOut << "\t\tcmp ax, 0\n";
                            fileOut << "\t\tjge " << rotPositivo << "\n";
                            fileOut << "\t\tmov bl, 2Dh\n";
                            fileOut << "\t\tadd di, 1\n";
                            fileOut << "\t\tneg ax\n";
                            fileOut << rotPositivo << ":\n";
                            fileOut << "\t\tmov bx, 10\n";
                            fileOut << rotLoop1 << ":\n";
                            fileOut << "\t\tadd cx, 1\n";
                            fileOut << "\t\tmov dx, 0\n";
                            fileOut << "\t\tidiv bx\n";
                            fileOut << "\t\tpush dx\n";
                            fileOut << "\t\tcmp ax, 0\n";
                            fileOut << "\t\tjne " << rotLoop1 << "\n";
                            fileOut << rotLoop2 << ":\n";
                            fileOut << "\t\tpop dx\n";
                            fileOut << "\t\tadd dx, 48\n";
                            fileOut << "\t\tmov ds:[di], dl\n";
                            fileOut << "\t\tadd di, 1\n";
                            fileOut << "\t\tadd cx, -1\n";
                            fileOut << "\t\tcmp cx, 0\n";
                            fileOut << "\t\tjne " << rotLoop2 << "\n";
                            // grava o fim da string "$"
                            fileOut << "\t\tmov dl, 24h\n";
                            fileOut << "\t\tmov DS:[di], dl\n";

                        }else
                            if(tabSimbNaoTerminais.search("EXPRESSAO")->tipo.compare("string")==0){

                                stringTempEnd = tabSimbNaoTerminais.search("EXPRESSAO")->end;

                            }
                        // mostra a string na tela
                        fileOut << "\t\tmov dx, " << stringTempEnd << "\n";
                        fileOut << "\t\tmov ah, 09h\n";
                        fileOut << "\t\tint 21h\n";

                    }

                }else notNull = false;
            }
       // }
    }

    // Geração de codigo
    if(quebraLinha){

        fileOut << "\t\tmov ah, 02h\n";
		fileOut << "\t\tmov dl, 0Dh\n";
		fileOut << "\t\tint 21h\n";
		fileOut << "\t\tmov dl, 0Ah\n";
		fileOut << "\t\tint 21h\n";

    }

	match('K');

}

/**
 *  Procedimento EXPRESSAO
 */
void SintAnalyzer::EXPRESSAO(){

    tabSimbNaoTerminais.insert(0, "EXPRESSAO");

	EXP_4();
	// Ação Semantica
	tabSimbNaoTerminais.search("EXPRESSAO")->tipo = tabSimbNaoTerminais.search("EXP_4")->tipo;
	// Geração de Codigo
	tabSimbNaoTerminais.search("EXPRESSAO")->end = tabSimbNaoTerminais.search("EXP_4")->end;


    if(currentToken != NULL){
        notNull = true;



       // if (currentToken->cod == 'A'){ // Operador Produzido

            while(notNull){ // enquanto proximo token for operador

                if(currentToken->cod == 'A'){ // Operador Produzido
                    string exp4Anterior = tabSimbNaoTerminais.search("EXP_4")->tipo;
                    int exp4EndAnterior = tabSimbNaoTerminais.search("EXP_4")->end;
                    LexRecord * operador = currentToken;
                    OPERADOR_P5();
                    EXP_4();
                    // Ação semantica
                    if(operador->lexema.compare("==")==0){
                        if((exp4Anterior.compare("string")==0 and tabSimbNaoTerminais.search("EXP_4")->tipo.compare("string")==0) or
                           ((exp4Anterior.compare("inteiro")==0 or exp4Anterior.compare("byte")==0) and
                            (tabSimbNaoTerminais.search("EXP_4")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_4")->tipo.compare("byte")==0))){

                                tabSimbNaoTerminais.search("EXPRESSAO")->tipo = "logico";
                        } else {
                                /**ERRO SEMANTICO**/
                                cout << operador->lineNumber << ":tipos incompatíveis.";
                        }
                    } else {
                        if((exp4Anterior.compare("inteiro")==0 or exp4Anterior.compare("byte")==0) and
                            (tabSimbNaoTerminais.search("EXP_4")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_4")->tipo.compare("byte")==0)){

                                tabSimbNaoTerminais.search("EXPRESSAO")->tipo = "logico";

                            } else {
                                /**ERRO SEMANTICO**/
                                cout << operador->lineNumber << ":tipos incompatíveis.";
                            }
                    }

                    // Geração de codigo
                    if(exp4Anterior.compare("string")==0){
                        fileOut << "\t\tmov di, " << exp4EndAnterior << "\n";
                        fileOut << "\t\tmov si, " << tabSimbNaoTerminais.search("EXP_4")->end << "\n";
                        string rotInicio = getLabel();
                        string rotVerdadeiro = getLabel();
                        string rotFalso = getLabel();
                        string rotFim = getLabel();
                        fileOut << rotInicio << ":\n";
                        fileOut << "\t\tmov al, DS:[di]\n";
                        fileOut << "\t\tmov bl, DS:[si]\n";
                        fileOut << "\t\tcmp al, 24h\n";
                        fileOut << "\t\tje " << rotFalso << "\n";
                        fileOut << "\t\tcmp bl, 24h\n";
                        fileOut << "\t\tje " << rotFalso << "\n";
                        fileOut << "\t\tcmp al, bl\n";
                        fileOut << "\t\tjne " << rotFalso << "\n";
                        fileOut << "\t\tadd di, 1\n";
                        fileOut << "\t\tadd si, 1\n";
                        fileOut << "\t\tjmp " << rotInicio << "\n";
                        fileOut << rotVerdadeiro << ":\n";
                        fileOut << "\t\tcmp bl, 24h\n";
                        fileOut << "\t\tjne " << rotFalso << "\n";
                        fileOut << "\t\tmov al, 255\n";
                        fileOut << "\t\tjmp " << rotFim << "\n";
                        fileOut << rotFalso << ":\n";
                        fileOut << "\t\tmov al, 0\n";
                        fileOut << rotFim << ":\n";
                        tabSimbNaoTerminais.search("EXPRESSAO")->end = tempCount;
                        updateTempCount(1);
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "], al\n";

                    } else {

                        if(exp4Anterior.compare("byte")==0){
                            fileOut << "\t\tmov al, DS:[" << exp4EndAnterior << "]\n";
                            fileOut << "\t\tmov ah, 0\n";
                        } else fileOut << "\t\tmov ax, DS:[" << exp4EndAnterior << "]\n";

                        if(tabSimbNaoTerminais.search("EXP_4")->tipo.compare("byte")==0){
                            fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_4")->end << "]\n";
                            fileOut << "\t\tmov bh, 0\n";
                        } else fileOut << "\t\tmov bx, DS:[" << tabSimbNaoTerminais.search("EXP_4")->end << "]\n";
                        fileOut << "\t\tcmp ax, bx\n";
                        string rotVerdadeiro = getLabel();

                        if(operador->lexema.compare("<")==0){
                            fileOut << "\t\tjl " << rotVerdadeiro << "\n";
                        } else
                            if(operador->lexema.compare("<=")==0){
                                fileOut << "\t\tjle " << rotVerdadeiro << "\n";
                            } else
                                if(operador->lexema.compare(">")==0){
                                    fileOut << "\t\tjg " << rotVerdadeiro << "\n";
                                } else
                                    if(operador->lexema.compare(">=")==0){
                                        fileOut << "\t\tjge " << rotVerdadeiro << "\n";
                                    } else
                                        if(operador->lexema.compare("==")==0){
                                            fileOut << "\t\tje " << rotVerdadeiro << "\n";
                                        } else
                                            if(operador->lexema.compare("<>")==0){
                                                fileOut << "\t\tjne " << rotVerdadeiro << "\n";
                                            }

                        fileOut << "\t\tmov al, 0\n";
                        string rotFim = getLabel();
                        fileOut << "\t\tjmp " << rotFim << "\n";
                        fileOut << rotVerdadeiro << ":\n";
                        fileOut << "\t\tmov al, 255\n";
                        fileOut << rotFim << ":\n";
                        tabSimbNaoTerminais.search("EXPRESSAO")->end = tempCount;
                        updateTempCount(1);
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXPRESSAO")->end << "], al\n";
                    }

                } else
                    notNull = false;
            }
        //}
    }
}

/**
 *  Procedimento OPERADOR_P5
 */
void SintAnalyzer::OPERADOR_P5(){
	match('A');
}


/**
 *  Procedimento EXP_4
 */
void SintAnalyzer::EXP_4(){

    bool negativo = false;
    tabSimbNaoTerminais.insert(0, "EXP_4");

    if(currentToken != NULL){

        if (currentToken->lexema.compare("-") == 0){

            match('C');
            negativo = true;
        }
    }
    LexRecord * token = currentToken;
	EXP_3();
	// Ação Semantica
	tabSimbNaoTerminais.search("EXP_4")->tipo = tabSimbNaoTerminais.search("EXP_3")->tipo;
	if(negativo){
        if(tabSimbNaoTerminais.search("EXP_3")->tipo.compare("inteiro")!=0){
            /**ERRO SEMANTICO**/
            cout << token->lineNumber << ":tipos incompatíveis.";
        }
        // Geração de codigo
        fileOut << "\t\tmov ax, DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "]\n";
        fileOut << "\t\tneg ax\n";
        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "], ax\n";
	}
	// Geração de Codigo
	tabSimbNaoTerminais.search("EXP_4")->end = tabSimbNaoTerminais.search("EXP_3")->end;


    if(currentToken != NULL){
        notNull = true;
      //  if ((currentToken->lexema.compare("-") == 0) || (currentToken->lexema.compare("+") == 0) || (currentToken->lexema.compare("or") == 0)){
            while(notNull){
                if((currentToken->lexema.compare("-") == 0) || (currentToken->lexema.compare("+") == 0) || (currentToken->lexema.compare("or") == 0)){

                    string exp3Anterior = tabSimbNaoTerminais.search("EXP_3")->tipo;
                    int exp3EndAnterior = tabSimbNaoTerminais.search("EXP_3")->end;
                    LexRecord * operador = currentToken;

                    OPERADOR_P4();
                    EXP_3();

                    // Ações semanticas
                    if(operador->lexema.compare("or")==0){
                        if(exp3Anterior.compare("logico")==0 and tabSimbNaoTerminais.search("EXP_3")->tipo.compare("logico")==0){
                            tabSimbNaoTerminais.search("EXP_4")->tipo = "logico";
                        } else {
                            /**ERRO SEMANTICO**/
                            cout << operador->lineNumber << ":tipos incompatíveis.";
                        }
                    } else
                        if(operador->lexema.compare("+")==0){
                                if((exp3Anterior.compare("string")==0 and tabSimbNaoTerminais.search("EXP_3")->tipo.compare("string")==0) or
                                    ((exp3Anterior.compare("inteiro")==0 or exp3Anterior.compare("byte")==0) and
                                    (tabSimbNaoTerminais.search("EXP_3")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0))){
                                        if(exp3Anterior.compare("string")==0){
                                            tabSimbNaoTerminais.search("EXP_4")->tipo = "string";
                                        }else
                                            if(exp3Anterior.compare("inteiro")==0){
                                                tabSimbNaoTerminais.search("EXP_4")->tipo = "inteiro";
                                            }else
                                                if(tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0){
                                                    tabSimbNaoTerminais.search("EXP_4")->tipo = "byte";
                                                }else{
                                                    tabSimbNaoTerminais.search("EXP_4")->tipo = "inteiro";
                                                }
                                    } else{
                                        /**ERRO SEMANTICO**/
                                        cout << operador->lineNumber << ":tipos incompatíveis.";
                                    }
                        } else
                            if(operador->lexema.compare("-")==0){
                                if((exp3Anterior.compare("inteiro")==0 or exp3Anterior.compare("byte")==0) and
                                    (tabSimbNaoTerminais.search("EXP_3")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0)){

                                        if(exp3Anterior.compare("inteiro")==0){
                                                tabSimbNaoTerminais.search("EXP_4")->tipo = "inteiro";
                                            }else
                                                if(tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0){
                                                    tabSimbNaoTerminais.search("EXP_4")->tipo = "byte";
                                                }else{
                                                    tabSimbNaoTerminais.search("EXP_4")->tipo = "inteiro";
                                                }
                                    } else{
                                        /**ERRO SEMANTICO**/
                                        cout << operador->lineNumber << ":tipos incompatíveis.";
                                    }
                            }

                    // Geração de codigo
                    if(tabSimbNaoTerminais.search("EXP_4")->tipo.compare("byte")==0){

                        fileOut << "\t\tmov al, DS:[" << exp3EndAnterior << "]\n";
                        fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "]\n";

                        if(operador->lexema.compare("+")==0){
                            fileOut << "\t\tadd al, bl\n";
                        } else
                            if(operador->lexema.compare("-")==0){
                                fileOut << "\t\tsub al, bl\n";
                            }
                        tabSimbNaoTerminais.search("EXP_4")->end = tempCount;
                        updateTempCount(1);
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_4")->end << "], al\n";

                    } else
                        if(exp3Anterior.compare("string")==0){

                            tabSimbNaoTerminais.search("EXP_4")->end = tempCount;
                            updateTempCount(256);
                            fileOut << "\t\tmov di, " << tabSimbNaoTerminais.search("EXP_4")->end << "\n";
                            fileOut << "\t\tmov si, " << exp3EndAnterior << "\n";
                            string rotInicio1 = getLabel();
                            string rotInicio2 = getLabel();

                            fileOut << rotInicio1 << ":\n";
                            fileOut << "\t\tmov al, DS:[si]\n";
                            fileOut << "\t\tmov DS:[di], al\n";
                            fileOut << "\t\tadd di, 1\n";
                            fileOut << "\t\tadd si, 1\n";
                            fileOut << "\t\tcmp al, 24h\n";
                            fileOut << "\t\tjne " << rotInicio1 << "\n";
                            fileOut << "\t\tmov si, " << tabSimbNaoTerminais.search("EXP_3")->end << "\n";
                            fileOut << "\t\tsub di, 1\n";

                            fileOut << rotInicio2 << ":\n";
                            fileOut << "\t\tmov al, DS:[si]\n";
                            fileOut << "\t\tmov DS:[di], al\n";
                            fileOut << "\t\tadd di, 1\n";
                            fileOut << "\t\tadd si, 1\n";
                            fileOut << "\t\tcmp al, 24h\n";
                            fileOut << "\t\tjne " << rotInicio2 << "\n";

                        } else
                            if(exp3Anterior.compare("logico")==0){

                                fileOut << "\t\tmov al, DS:[" << exp3EndAnterior << "]\n";
                                fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "]\n";
                                fileOut << "\t\tor al, bl\n";
                                tabSimbNaoTerminais.search("EXP_4")->end = tempCount;
                                updateTempCount(1);
                                fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_4")->end << "], al\n";

                            } else {

                                if(exp3Anterior.compare("byte")==0){
                                    fileOut << "\t\tmov al, DS:[" << exp3EndAnterior << "]\n";
                                    fileOut << "\t\tmov ah, 0\n";
                                } else fileOut << "\t\tmov ax, DS:[" << exp3EndAnterior << "]\n";

                                if(tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0){
                                    fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "]\n";
                                    fileOut << "\t\tmov bh, 0\n";
                                } else fileOut << "\t\tmov bx, DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "]\n";

                                if(operador->lexema.compare("+")==0){
                                    fileOut << "\t\tadd ax, bx\n";
                                } else
                                    if(operador->lexema.compare("-")==0){
                                        fileOut << "\t\tsub ax, bx\n";
                                    }
                                tabSimbNaoTerminais.search("EXP_4")->end = tempCount;
                                updateTempCount(2);
                                fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_4")->end << "], ax\n";

                            }


                } else notNull = false;
            }
       // }
    }
}

/**
 *  Procedimento OPERADOR_P4
 */
void SintAnalyzer::OPERADOR_P4(){
    if(currentToken != NULL){
        if ((currentToken->lexema.compare("-") == 0) || (currentToken->lexema.compare("+") == 0))
            match('C');
        else
            match('J');
    }
}

/**
 * Procedimento EXP_3
 */
void SintAnalyzer::EXP_3(){

	tabSimbNaoTerminais.insert(0, "EXP_3");

	EXP_2();

	// Ação Semantica
	tabSimbNaoTerminais.search("EXP_3")->tipo = tabSimbNaoTerminais.search("EXP_2")->tipo;
	// Geração de Codigo
	tabSimbNaoTerminais.search("EXP_3")->end = tabSimbNaoTerminais.search("EXP_2")->end;

    if(currentToken != NULL){

        //if ((currentToken->lexema.compare("*") == 0) | (currentToken->lexema.compare("/") == 0) | (currentToken->lexema.compare("and") == 0)){
            while(notNull){

                if((currentToken->lexema.compare("*") == 0) or (currentToken->lexema.compare("/") == 0) or (currentToken->lexema.compare("and") == 0)){

                    string exp2Anterior = tabSimbNaoTerminais.search("EXP_2")->tipo;
                    int exp2EndAnterior = tabSimbNaoTerminais.search("EXP_2")->end;
                    LexRecord * operador = currentToken;

                    OPERADOR_P3();
                    EXP_2();

                    // Ações Semanticas
                    if(operador->lexema.compare("and")==0){

                        if(exp2Anterior.compare("logico")==0 and tabSimbNaoTerminais.search("EXP_2")->tipo.compare("logico")==0){
                            tabSimbNaoTerminais.search("EXP_3")->tipo = "logico";

                        } else{
                            /**ERRO SEMANTICO**/
                            cout << operador->lineNumber << ":tipos incompatíveis.";

                        }
                    } else
                        if(operador->lexema.compare("/")==0){

                            if((exp2Anterior.compare("inteiro")==0 or exp2Anterior.compare("byte")==0) and
                            (tabSimbNaoTerminais.search("EXP_2")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_2")->tipo.compare("byte")==0)){

                                tabSimbNaoTerminais.search("EXP_3")->tipo = "inteiro";

                            } else{
                                /**ERRO SEMANTICO**/
                                cout << operador->lineNumber << ":tipos incompatíveis.";

                            }
                        } else
                            if(operador->lexema.compare("*")==0){

                                if(exp2Anterior.compare("byte")==0 and tabSimbNaoTerminais.search("EXP_2")->tipo.compare("byte")==0){

                                    tabSimbNaoTerminais.search("EXP_3")->tipo = "byte";

                                }else
                                    if((exp2Anterior.compare("inteiro")==0 or exp2Anterior.compare("byte")==0) and
                                    (tabSimbNaoTerminais.search("EXP_2")->tipo.compare("inteiro")==0 or tabSimbNaoTerminais.search("EXP_2")->tipo.compare("byte")==0)){

                                        tabSimbNaoTerminais.search("EXP_3")->tipo = "inteiro";

                                    } else{
                                        /**ERRO SEMANTICO**/
                                        cout << operador->lineNumber << ":tipos incompatíveis.";

                                    }
                            }

                    // Geração de codigo
                    if(exp2Anterior.compare("logico")==0){

                        fileOut << "\t\tmov al, DS:[" << exp2EndAnterior << "]\n";
                        fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";
                        fileOut << "\t\tand al, bl\n";
                        tabSimbNaoTerminais.search("EXP_3")->end = tempCount;
                        updateTempCount(1);
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "], al\n";

                    }else
                        if(operador->lexema.compare("/")==0){

                            if(exp2Anterior.compare("byte")==0){

                                fileOut << "\t\tmov al, DS:[" << exp2EndAnterior << "]\n";
                                fileOut << "\t\tmov ah, 0\n";
                                fileOut << "\t\tmov dx, 0\n";

                            } else {

                                fileOut << "\t\tmov ax, DS:[" << exp2EndAnterior << "]\n";
                                fileOut << "\t\tmov dx, 0\n";

                            }

                            if(tabSimbNaoTerminais.search("EXP_2")->tipo.compare("byte")==0){

                                fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";
                                fileOut << "\t\tmov bh, 0\n";
                                fileOut << "\t\tmov dx, 0\n";

                            } else {

                                fileOut << "\t\tmov bx, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";
                                fileOut << "\t\tmov dx, 0\n";

                            }

                            tabSimbNaoTerminais.search("EXP_3")->end = tempCount;
                            updateTempCount(2);
                            fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "], ax\n";

                        }else
                            if(operador->lexema.compare("*")==0){

                                if(tabSimbNaoTerminais.search("EXP_3")->tipo.compare("byte")==0){

                                    fileOut << "\t\tmov al, DS[" << exp2EndAnterior << "]\n";
                                    fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";
                                    fileOut << "\t\tmul bl\n";
                                    tabSimbNaoTerminais.search("EXP_3")->end = tempCount;
                                    updateTempCount(1);
                                    fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "], al\n";

                                }else {

                                    if(exp2Anterior.compare("byte")==0){

                                        fileOut << "\t\tmov al, DS:[" << exp2EndAnterior << "]\n";
                                        fileOut << "\t\tmov ah, 0\n";

                                    } else {

                                        fileOut << "\t\tmov ax, DS:[" << exp2EndAnterior << "]\n";

                                    }

                                    if(tabSimbNaoTerminais.search("EXP_2")->tipo.compare("byte")==0){

                                        fileOut << "\t\tmov bl, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";
                                        fileOut << "\t\tmov bh, 0\n";

                                    } else {

                                        fileOut << "\t\tmov bx, DS:[" << tabSimbNaoTerminais.search("EXP_2")->end << "]\n";

                                    }

                                    fileOut << "\t\timul bx\n";
                                    tabSimbNaoTerminais.search("EXP_3")->end = tempCount;
                                    updateTempCount(2);
                                    fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_3")->end << "], ax\n";

                                }
                            }

                } else notNull = false;
            }
        //}
    }
}


/**
 *  Procedimento OPERADOR_P3
 */
void SintAnalyzer::OPERADOR_P3(){
    if(currentToken != NULL){
        if ((currentToken->lexema.compare("*") == 0) || (currentToken->lexema.compare("/") == 0))
            match('C');
        else
            match('J');
    }
}


/**
 *  Procedimento EXP_2
 */
void SintAnalyzer::EXP_2(){

    bool negado = false;
    tabSimbNaoTerminais.insert(0, "EXP_2");
    LexRecord * token = currentToken;

    if(currentToken != NULL){

        if ((currentToken->lexema.compare("not") == 0)){

            negado = true;
            match('J');
        }
    }

	EXP_1();

	// Ação Semantica
	tabSimbNaoTerminais.search("EXP_2")->tipo = tabSimbNaoTerminais.search("EXP_1")->tipo;
	if(negado){

        if(tabSimbNaoTerminais.search("EXP_1")->tipo.compare("logico")!=0){
            /**ERRO SEMANTICO**/
            cout << token->lineNumber << ":tipos incompatíveis.";
        }

        // Geração de codigo
        fileOut << "\t\tmov al, DS:[" << tabSimbNaoTerminais.search("EXP_1")->end << "]\n";
        fileOut << "\t\tnot al\n";
        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("EXP_1")->end << "], al\n";
	}

	// Geração de codigo
	tabSimbNaoTerminais.search("EXP_2")->end = tabSimbNaoTerminais.search("EXP_1")->end;
}


/**
 *  Procedimento EXP_1
 */
void SintAnalyzer::EXP_1(){

    tabSimbNaoTerminais.insert(0, "EXP_1");

    if(currentToken != NULL){

        if (currentToken->cod == '8'){

            match('8');
            EXPRESSAO();


            // Ação Semantica
            tabSimbNaoTerminais.search("EXP_1")->tipo = tabSimbNaoTerminais.search("EXPRESSAO")->tipo;


            // Geração de codigo
            tabSimbNaoTerminais.search("EXP_1")->end = tabSimbNaoTerminais.search("EXPRESSAO")->end;


            match('9');


        }
        else{

            CONST();

            // Ação Semantica
            tabSimbNaoTerminais.search("EXP_1")->tipo = tabSimbNaoTerminais.search("CONST")->tipo;

            // Geração de codigo
            tabSimbNaoTerminais.search("EXP_1")->end = tabSimbNaoTerminais.search("CONST")->end;
        }

    }



}


/**
 *  Procedimento CONST
 */
void SintAnalyzer::CONST(){

    tabSimbNaoTerminais.insert(0, "CONST");

    if(currentToken != NULL){

        tabSimbNaoTerminais.search("CONST")->end = tempCount;

        if (currentToken->cod == 'F'){ //inteiro

            // Ação Semantica
            tabSimbNaoTerminais.search("CONST")->tipo = "inteiro";

            // Geração de codigo
            fileOut << "\t\tmov cx, " << currentToken->lexema << "\n";
            fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], cx\n";
            updateTempCount(2);

            match('F');

        }else
            if (currentToken->cod == 'M' || currentToken->cod == 'I'){ //byte

                // Ação Semantica
                tabSimbNaoTerminais.search("CONST")->tipo = "byte";

                // Geração de codigo
                fileOut << "\t\tmov cl, " << currentToken->lexema << "\n";
                fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], cl\n";
                updateTempCount(1);

                match('M');

            }else
                if (currentToken->cod == 'L'){ //logico

                    // Ação Semantica
                    tabSimbNaoTerminais.search("CONST")->tipo = "logico";

                    // Geração de codigo
                    if(currentToken->lexema.compare("TRUE")==0){

                        fileOut << "\t\tmov cl, 255\n";
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], cl\n";

                    } else {

                        fileOut << "\t\tmov cl, 0\n";
                        fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], cl\n";

                    }
                    updateTempCount(1);

                    match('L');

                }else
                    if (currentToken->cod == 'N'){ //string

                        // Ação Semantica
                        tabSimbNaoTerminais.search("CONST")->tipo = "string";

                        // Geração de Codigo
                        int stringEnd = dataCount;
                        fileOut << "dseg SEGMENT PUBLIC\n";
                        fileOut << "\t\tbyte " << currentToken->lexema << "\n";
                        fileOut << "dseg ENDS\n";
                        updateDataCount(currentToken->lexema.length()-2);
                        fileOut << "\t\tmov si, " << stringEnd << "\n";
                        fileOut << "\t\tmov di, " << tabSimbNaoTerminais.search("CONST")->end << "\n";
                        string rotInicio = getLabel();
                        fileOut << rotInicio << ":\n";
                        fileOut << "\t\tmov al, DS:[si]\n";
                        fileOut << "\t\tmov DS:[di], al\n";
                        fileOut << "\t\tadd di, 1\n";
                        fileOut << "\t\tadd si, 1\n";
                        fileOut << "\t\tcmp al, 24h\n";
                        fileOut << "\t\tjne " << rotInicio << "\n";
                        updateTempCount(256);

                        match('N');

                    }else
                        if (currentToken->cod == 'H' || currentToken->cod == 'I'){ //identificador

                            // Ação Semantica
                            if(currentToken->adressTable->classe.compare("vazio")!=0){

                                tabSimbNaoTerminais.search("CONST")->tipo = currentToken->adressTable->tipo;

                            } else {
                                /**ERRO SEMANTICO**/
                                cout << currentToken->lineNumber << ":identificador nao declarado [" << currentToken->lexema << "].";

                            }

                            if(currentToken->adressTable->tipo.compare("inteiro")==0){

                                // Geração de codigo
                                fileOut << "\t\tmov ax, DS:[" << currentToken->adressTable->end << "]\n";
                                fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], ax\n";
                                updateTempCount(2);

                            } else
                                if(currentToken->adressTable->tipo.compare("string")==0){

                                    // Geração de codigo
                                    fileOut << "\t\tmov si, " << currentToken->adressTable->end << "\n";
                                    fileOut << "\t\tmov di, " << tabSimbNaoTerminais.search("CONST")->end << "\n";
                                    string rotInicio = getLabel();
                                    fileOut << rotInicio << ":\n";
                                    fileOut << "\t\tmov al, DS:[si]\n";
                                    fileOut << "\t\tmov DS:[di], al\n";
                                    fileOut << "\t\tadd di, 1\n";
                                    fileOut << "\t\tadd si, 1\n";
                                    fileOut << "\t\tcmp al, 24h\n";
                                    fileOut << "\t\tjne " << rotInicio << "\n";
                                    updateTempCount(256);

                                } else{

                                    // Geração de codigo
                                    fileOut << "\t\tmov al, DS:[" << currentToken->adressTable->end << "]\n";
                                    fileOut << "\t\tmov DS:[" << tabSimbNaoTerminais.search("CONST")->end << "], al\n";
                                    updateTempCount(1);

                                }

                            match('H');

                        }
    }

}

/**
 *  Metodo casaToken
 */
void SintAnalyzer::match(char tipo){

	if(currentToken == NULL){
      	cout << registroLexico.getLastToken()->lineNumber << ":fim de arquivo nao esperado";
	}
	else {
            cout << "token: " << tipo << " - " << currentToken->cod << "\n";
		if(currentToken->cod == 'I'){
			if(tipo == 'H' || tipo == 'M')
				currentToken->cod = tipo;
		}
		if(currentToken->cod == tipo){
			currentToken = registroLexico.getNextToken();
			if(currentToken == NULL)
                notNull = false;
                else
                    notNull = true;
		} else {
			cout << currentToken->lineNumber << ":token nao esperado [" << currentToken->lexema << "].";
		}
	}
}

/**
 *  metodo que atualiza a posicao de temporario valida
 */
 void SintAnalyzer::updateTempCount(int v){
    tempCount += v;
 }

/**
 *  metodo que atualiza a posicao de memoria valida
 */
 void SintAnalyzer::updateDataCount(int v){
    dataCount += v;
 }

/**
 *  metodo que retorna o proximo rotulo disponivel
 */
 std::string SintAnalyzer::getLabel(){

    std::ostringstream stm;
    stm << labelCount++;
    return "R" + stm.str();

}

/**
 * metodo que inicia a analise da gramatica
 */
void SintAnalyzer::principal(/*const char *arq*/){
	lex.lerArq("exemplo.l");

	registroLexico = lex.getRegLexico();
	//tabelaSimbolo = lex.getTabelaSimbolo();
	registroLexico.resetNext();
	currentToken = registroLexico.getNextToken();
	notNull = true;
    fileOut.open("saida.asm");
    tempCount = 0;
    dataCount = 16384;
    labelCount = 1;
	S();
	//cout << currentToken->cod;
	if(currentToken != NULL)
        cout << currentToken->lineNumber << ":token nao esperado [" << currentToken->lexema << "].";

	//cout << "\n\nteste: " << currentToken->cod << "\n\n";
	//cout << "\n\nteste: " << currentToken->lexema << "\n\n";

	//cout << "\n\nteste: " << currentToken->next->cod << "\n\n";

}//end principal


