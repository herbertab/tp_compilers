// Exemplo de Programa na linguagem L

integer n;
string nome;
boolean naoTerminou;
const MAXITER=3;

// Bloco Principal

{  
  naoTerminou = TRUE;
  while naoTerminou {
    writeln, "Teste Compiladores";
    writeln, "Escolha uma opcao:";
    write, "1 Teste if ", "2 Teste Atribuicao ";
    writeln, "3 Termina";
    readln, n;
    if n == 1 then
      writeln, "IF Ok";
      else if n == 2 then {
        nome = "Atribuicao OK";
        writeln, nome;
    } else if n == 3 then
        naoTerminou = FALSE;
   else 
  writeln, "Opcao invalida";
  }
}