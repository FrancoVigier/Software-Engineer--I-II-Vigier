:- dec_type(mensaje, str).
:- dec_type(msglista,set([user,mensaje])).
:- dec_type(casilla, rel(user,msglista)).


%Axioma de Capacidad de los buzones.
:- dec_p_type(capMaxima(int)).
capMaxima(X) :- 0 =< X & X =< 2.

%Gestor de Mails, init. 
:- dec_p_type(gestorMailsInit(casilla,casilla,casilla)).
gestorMailsInit(UsersNewMails,UsersReadMails,UsersSendMails) :-
     UsersNewMails = {} &
     UsersReadMails = {} &
     UsersSendMails = {} .

:- dec_p_type(conditionInv(casilla, user)).
conditionInv(CasillaMail,X1) :-
     dec(M1, msglista) & 
     dec(N1, int) & 
     [X1,M1] in CasillaMail &
     size(M1, N1) & 
     capMaxima(N1).

%Gestos de Mails, inv. 
:- dec_p_type(gestorMailsInv(casilla, casilla, casilla)).
gestorMailsInv(UsersNewMails,UsersReadMails,UsersSendMails) :-
%Invariante de que los dominios de las casillas tienen que ser iguales, asi todos los usuarios tienen las 3 casillas, por lo tanto deriva en que nunca vamos a poder leer, mandar o leer un mensaje de un usuario que no tenga las 3 casillas y porque vamos a tener un estado de casilla inconsistente
%en la demostracion del teorema sendmsg: si metemos todas casillas simbolicas obviamente sabiendo que los dominios son iguales va a tomar el minimo posible el unitario y va  a igualar los dos usuarios que se mandan mensaje      
     dec(NM, set(user)) &
     dec(RM, set(user)) &
     dec(SM, set(user)) & 
     dom(UsersNewMails, NM) &
     dom(UsersReadMails,RM) &
     dom(UsersSendMails,SM) &
     NM = RM &
     RM = SM &
     SM = NM &
%Invariante del largo de las casillas. 
     dec(X1,user) &
     dec(X2,user) & 
     dec(X3,user) &
     foreach(X1 in NM,conditionInv(UsersNewMails,X1)) &
     foreach(X2 in RM,conditionInv(UsersReadMails,X2)) &
     foreach(X3 in SM,conditionInv(UsersSendMails,X3)) .
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%SENDMSG%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%SendMsgOk, es como que traemos Variables que ya cumplen con el predicado y las uso. 
:- dec_p_type(sendMsgOk(casilla, casilla, casilla,user,user,mensaje,casilla,casilla,casilla)).
sendMsgOk(UsersNewMails,UsersReadMails,UsersSendMails,To_i,From_i,Body_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
%Verificamos que los involucrados estén entre los usuarios
     dec(A, set(user)) &
     dec(AA, set(user)) &
     dom(UsersNewMails,A) & 
     dom(UsersSendMails,AA) &
     To_i in A &
     From_i in AA  &
%Verificamos el tamaño de las casilla del destino, reemplazo el apply por las simulaciones
     dec(BuzonTo,msglista) &
     [To_i,BuzonTo] in UsersNewMails &
     dec(TamanoBuzonTo,int) &
     size(BuzonTo,TamanoBuzonTo) &
     capMaxima(TamanoBuzonTo + 1) &
%Verificamos el tamaño de la casilla del origen
     dec(BuzonSend,msglista) &
     [From_i,BuzonSend] in UsersSendMails &
     dec(TamanoBuzonSend,int) &
     size(BuzonSend,TamanoBuzonSend) &
     capMaxima(TamanoBuzonSend + 1) &
%Modificamos las casillas del que manda
     dec(C,msglista) &
     un(BuzonSend,{[To_i,Body_i]},C) &
     oplus(UsersSendMails,{[From_i,C]},UsersSendMails_) &
%Modificamos las casillas del que recibe
     dec(D,msglista) &
     un(BuzonTo,{[From_i,Body_i]},D) &
     oplus(UsersNewMails,{[To_i,D]},UsersNewMails_) &
%La casilla de lectura inmuta
     UsersReadMails_ = UsersReadMails .

:- dec_p_type(emisorUnreachable(casilla, casilla, casilla,user,casilla,casilla,casilla)).
emisorUnreachable(UsersNewMails,UsersReadMails,UsersSendMails,From_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)  :- 
     dec(A, set(user)) &
     dom(UsersSendMails,A)&
     From_i nin A &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

:- dec_p_type(destinoUnreachable(casilla, casilla, casilla,user,casilla,casilla,casilla)).
destinoUnreachable(UsersNewMails,UsersReadMails,UsersSendMails,To_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(A, set(user)) &
     dom(UsersNewMails,A) &
     To_i nin A &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

:- dec_p_type(fullSendBox(casilla, casilla, casilla,user,casilla,casilla,casilla)).
fullSendBox(UsersNewMails,UsersReadMails,UsersSendMails,From_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(BuzonSend,msglista) &
     dec(TamanoBuzonSend, int) &
     [From_i,BuzonSend] in UsersSendMails &
     size(BuzonSend,TamanoBuzonSend) &
     neg (capMaxima(TamanoBuzonSend + 1)) &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

:- dec_p_type(fullNewBox(casilla, casilla, casilla,user,casilla,casilla,casilla)).
fullNewBox(UsersNewMails,UsersReadMails,UsersSendMails,To_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(BuzonTo,msglista) &
     dec(TamanoBuzonTo, int) &
     [To_i,BuzonTo] in UsersNewMails &
     size(BuzonTo,TamanoBuzonTo) &
     neg(capMaxima(TamanoBuzonTo + 1)) &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

%SendMgsNoOK, predicados bajo la cual no alteramos el estado ni mandamos los mensajes. 
:- dec_p_type(sendMgsNoOk(casilla, casilla, casilla,user,user,mensaje,casilla,casilla,casilla)).
sendMgsNoOk(UsersNewMails,UsersReadMails,UsersSendMails,To_i,From_i,Body_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
   %Emisor No Alcanzable
       emisorUnreachable(UsersNewMails,UsersReadMails,UsersSendMails,From_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) 
   or
   %Destino No Alcanzable
       destinoUnreachable(UsersNewMails,UsersReadMails,UsersSendMails,To_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) 
   or
 %  Full Casilla de mail del emisor
       fullSendBox(UsersNewMails,UsersReadMails,UsersSendMails,From_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
   or
   %Full Casilla de mail del receptor
       fullNewBox(UsersNewMails,UsersReadMails,UsersSendMails,To_i,UsersNewMails_,UsersReadMails_,UsersSendMails_).

%SendMsg: La operacion TOTAL del envio de un mensaje. 
:- dec_p_type(sendMsg(casilla, casilla, casilla,user,user,mensaje,casilla,casilla,casilla)).
sendMsg(UsersNewMails,UsersReadMails,UsersSendMails,To_i,From_i,Body_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     sendMsgOk(UsersNewMails,UsersReadMails,UsersSendMails,To_i,From_i,Body_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
     or
     sendMgsNoOk(UsersNewMails,UsersReadMails,UsersSendMails,To_i,From_i,Body_i,UsersNewMails_,UsersReadMails_,UsersSendMails_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%READMSG%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%ReadMsgOk toma un mensaje de la casilla de nuevos lo pasa a la casilla de leidos y lo saca por una var output. 
:- dec_p_type(readMsgOk(casilla, casilla, casilla,user,mensaje,casilla,casilla,casilla)).
readMsgOk(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,Msg_o,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
%Este el lector en los dominios a trabajar     
     dec(ND, set(user)) &
     dom(UsersNewMails,ND) &
     Lector_i in ND &
     dec(RD, set(user)) &
     dom(UsersReadMails,RD) &
     Lector_i in RD &
%Obtenemos el buzon New del usuario
     dec(BuzonNuevosLector,msglista) &
     [Lector_i,BuzonNuevosLector] in UsersNewMails &
%Obtenemos el buzon Read del usuario
     dec(BuzonLeidosLector,msglista) &
     [Lector_i,BuzonLeidosLector] in UsersReadMails &
%Probamos que haya mensajes en el buzon New del usuario
     dec(MsgSinLeer, int) &
     size(BuzonNuevosLector, MsgSinLeer) &
     1 =< MsgSinLeer &
%Sacamos un mensaje del buzon New y lo sacamos por el output
     dec(M,mensaje) &
     dec(X, user) &
     [X,M] in BuzonNuevosLector &
     Msg_o = M &
%Vemos que el buzon Read del usuario tenga capacidad 
     dec(N,int) &
     size(BuzonLeidosLector, N) &
     capMaxima(N+1) &
%Sacamos el mensaje del buzon New y lo pasamos al buzon Read
     dec(NuevoBuzonLector,msglista) &
     BuzonNuevosLector = {[X,M]/ NuevoBuzonLector} &
     [X,M] nin  NuevoBuzonLector &    %%%% or [X,M] nin BuzonNuevosLector & NuevoBuzonLector = BuzonNuevosLector &. Forma de no usar el diff que tira corte en la simulacion no haciendo que sea solo un caso
     
     dec(NuevoBuzonLeidosLector,msglista) & 
     un(BuzonLeidosLector, {[X,M]},NuevoBuzonLeidosLector) &     
     
     oplus(UsersNewMails,{[Lector_i,NuevoBuzonLector]},UsersNewMails_) &
     oplus(UsersReadMails,{[Lector_i,NuevoBuzonLeidosLector]},UsersReadMails_) &
     UsersSendMails_ = UsersSendMails .

:- dec_p_type(lectorNotFound(casilla, casilla, casilla,user,casilla,casilla,casilla)).
lectorNotFound(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(ND, set(user)) &
     dec(RD, set(user)) &
     dom(UsersNewMails,ND) &
     dom(UsersReadMails,RD) &
     (Lector_i nin RD or
     Lector_i nin ND) &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

:- dec_p_type(newBoxEmpty(casilla, casilla, casilla,user,casilla,casilla,casilla)).
newBoxEmpty(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(BuzonNuevosLector,msglista) &
     dec(MsgSinLeer,int) &
     [Lector_i,BuzonNuevosLector] in UsersNewMails &
     size(BuzonNuevosLector, MsgSinLeer) &
     0 = MsgSinLeer &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

:- dec_p_type(readBoxFull(casilla, casilla, casilla,user,casilla,casilla,casilla)).
readBoxFull(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :- 
     dec(BuzonLeidosLector,msglista) &
     dec(N,int) &
     [Lector_i,BuzonLeidosLector] in UsersReadMails &
     size(BuzonLeidosLector, N) &
     neg(capMaxima(N+1)) &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails &
     UsersSendMails_=UsersSendMails .

%ReadMsgNoOk: clausulas por la cual no se efectua la correcta ejecucion de la lectura. 
:- dec_p_type(readMsgNoOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
readMsgNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
    %Lector no en dominio
    lectorNotFound(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) 
    or
    %Error de casilla de recibidos vacia
    newBoxEmpty(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
    or
    %Error de casilla de leidos llena
    readBoxFull(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%readMsg: clausula TOTAL de lectura de mails. 
:- dec_p_type(readMsg(casilla, casilla, casilla,user,mensaje,casilla,casilla,casilla)).
readMsg(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,Msg_o,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
      readMsgOk(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,Msg_o,UsersNewMails_,UsersReadMails_,UsersSendMails_)
      or
      readMsgNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Lector_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%cleanReadBox%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%cleanReadBoxOk: clausula bajo se limpia la readBox R, solo controlo que el usuario tenga dicha casilla porque si la tiene significa que tiene las otras porque todo usuario tiene las 3 casillas. 
:- dec_p_type(cleanReadBoxOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanReadBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     %Controlo que el usuario tenga una casilla de leidos
     dec(A,set(user)) &
     dom(UsersReadMails,A) &
     Usuario_i in A &
     %Borro su casilla
     oplus(UsersReadMails,{[Usuario_i,{}]},UsersReadMails_) &
     UsersNewMails_=UsersNewMails &
     UsersSendMails_=UsersSendMails .

%cleanReadBoxNoOk: clausula bajo la que no se limpia la readBox
:- dec_p_type(cleanReadBoxNoOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanReadBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     dec(A,set(user)) &
     dom(UsersReadMails,A) &
     Usuario_i nin A &
     UsersReadMails_ = UsersReadMails &
     UsersNewMails_=UsersNewMails &
     UsersSendMails_=UsersSendMails .

%cleanReadBox: clausula total
:- dec_p_type(cleanReadBox(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanReadBox(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     cleanReadBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
     or
     cleanReadBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%cleanSendBox%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%cleanSendBoxOk: clausula bajo se limpia la sendBox S, solo controlo que el usuario tenga dicha casilla porque si la tiene significa que tiene las otras porque todo usuario tiene las 3 casillas. 
:- dec_p_type(cleanSendBoxOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanSendBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     %Controlo que el usuario tenga una casilla de enviados
     dec(A,set(user)) &
     dom(UsersSendMails,A) &
     Usuario_i in A &
     %Borro su casilla
     oplus(UsersSendMails,{[Usuario_i,{}]},UsersSendMails_) &
     UsersNewMails_=UsersNewMails &
     UsersReadMails_=UsersReadMails .

%cleanSendBoxNoOk: clausula bajo la que no se limpia la sendBox
:- dec_p_type(cleanSendBoxNoOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanSendBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     dec(A,set(user)) &
     dom(UsersSendMails,A) &
     Usuario_i nin A &
     UsersReadMails_ = UsersReadMails &
     UsersNewMails_=UsersNewMails &
     UsersSendMails_=UsersSendMails .

%cleanSendBox: clausula total
:- dec_p_type(cleanSendBox(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanSendBox(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     cleanSendBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
     or
     cleanSendBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%cleanNewBox%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%cleanNewBoxOk: clausula bajo se limpia la newBox N, solo controlo que el usuario tenga dicha casilla porque si la tiene significa que tiene las otras porque todo usuario tiene las 3 casillas. 
:- dec_p_type(cleanNewBoxOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanNewBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     %Controlo que el usuario tenga una casilla de enviados
     dec(A,set(user)) &
     dom(UsersNewMails,A) &
     Usuario_i in A &
     %Borro su casilla
     oplus(UsersNewMails,{[Usuario_i,{}]},UsersNewMails_) &
     UsersSendMails_=UsersSendMails &
     UsersReadMails_=UsersReadMails .

%cleanNewBoxNoOk: clausula bajo la que no se limpia la newBox
:- dec_p_type(cleanNewBoxNoOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanNewBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
      dec(A,set(user)) &
     dom(UsersNewMails,A) &
     Usuario_i nin A &
     UsersReadMails_ = UsersReadMails &
     UsersNewMails_=UsersNewMails &
     UsersSendMails_=UsersSendMails .

%cleanNewBox: clausula total
:- dec_p_type(cleanNewBox(casilla, casilla, casilla,user,casilla,casilla,casilla)).
cleanNewBox(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     cleanNewBoxOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
     or
     cleanNewBoxNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%addUser%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%addUserOk: clausula por la que si se agrega un usuario
:- dec_p_type(addUserOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
addUserOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
     dec(A,set(user)) &
     dec(AA,set(user)) &
     dec(AAA,set(user)) &
     dom(UsersNewMails,A) &
     dom(UsersReadMails,AA) &
     dom(UsersSendMails,AAA) &

     %El usuario a agregar no esta
     Usuario_i nin A &
     Usuario_i nin AA & 
     Usuario_i nin AAA &

    %Actualizamos el estado
    un(UsersNewMails,{[Usuario_i,{}]},UsersNewMails_) &
    un(UsersSendMails,{[Usuario_i,{}]},UsersSendMails_) &
    un(UsersReadMails,{[Usuario_i,{}]},UsersReadMails_) .

:- dec_p_type(userInMail(casilla, casilla, casilla,user,casilla,casilla,casilla)).
userInMail(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
      dec(A,set(user)) &
      dec(AA,set(user)) &
      dec(AAA,set(user)) &
      dom(UsersNewMails,A) &
      dom(UsersReadMails,AA) &
      dom(UsersSendMails,AAA) &
      (Usuario_i in A 
       or
       Usuario_i in AA
       or
       Usuario_i in AAA) &
      UsersReadMails_ = UsersReadMails &
      UsersNewMails_=UsersNewMails &
      UsersSendMails_=UsersSendMails .

%addUserNoOk: clausula por la que no se agrega un usuario al gestor de mail
:- dec_p_type(addUserNoOk(casilla, casilla, casilla,user,casilla,casilla,casilla)).
addUserNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_):-
     userInMail(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) .

%addUser: clausula total
:- dec_p_type(addUser(casilla, casilla, casilla,user,casilla,casilla,casilla)).
addUser(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_) :-
      addUserOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_)
      or
      addUserNoOk(UsersNewMails,UsersReadMails,UsersSendMails,Usuario_i,UsersNewMails_,UsersReadMails_,UsersSendMails_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%SIMULACION2. TIPADA%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Con entorno no nulo, pero bien formulado que respete invariantes
:- dec_p_type(checkState(casilla, casilla, casilla,user,user)).
checkState(N,R,S,Usr1,Usr2) :- 
  N = {[Usr1, {[Usr1,"Borrador"],[Usr2,"hola usr1"]}] , [Usr2,{[Usr1, "chau usr2"]}] } &
  R = {[Usr1,{}],[Usr2,{}]} &
  S = {[Usr2, {[Usr1,"hola usr1"]}] , [Usr1,{[Usr2, "chau usr2"],[Usr1,"Borrador"]}] }  .

:- dec_p_type(simulacion2(user,user,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla)).
simulacion2(Usr1,Usr2,NewBoxInit,ReadBoxInit,SendBoxInit, NewBox2,ReadBox2,SendBox2,
                                              NewBox3,ReadBox3,SendBox3,NewBox4,ReadBox4,SendBox4,
                                              NewBox5,ReadBox5,SendBox5,NewBox6,ReadBox6,SendBox6,
                                              NewBox7,ReadBox7,SendBox7,NewBox8,ReadBox8,SendBox8 ):-

checkState(NewBoxInit,ReadBoxInit,SendBoxInit,Usr1,Usr2) &
Usr1 neq Usr2 &
gestorMailsInv(NewBoxInit,ReadBoxInit,SendBoxInit) &  %Verifico que el estado que verificamos en el check state cumple con la Invariate 

 readMsg(NewBoxInit,ReadBoxInit,SendBoxInit,Usr1,PrimerMsg,NewBox2,ReadBox2,SendBox2)  &
 dec(PrimerMsg,mensaje) &
 PrimerMsg = "Borrador" & % o sea se puede sacar cualquiera mientras sea perteneciente a un partes de la casilla del usuario
 readMsg(NewBox2,ReadBox2,SendBox2,Usr2,SegundoMsg,NewBox3,ReadBox3,SendBox3) &
 dec(SegundoMsg,mensaje) & 
SegundoMsg = "chau usr2" &
 readMsg(NewBox3,ReadBox3,SendBox3,Usr1,TercerMsg,NewBox4,ReadBox4,SendBox4) &
 dec(TercerMsg,mensaje) &
 TercerMsg = "hola usr1" &
%Solo con limpiar las casillas de leidos y enviados,  deberian quedar las 3 casillas vacias porque vaciamos la de nuevos a mano
 cleanReadBox(NewBox4,ReadBox4,SendBox4,Usr1,NewBox5,ReadBox5,SendBox5) &
 cleanSendBox(NewBox5,ReadBox5,SendBox5,Usr1,NewBox6,ReadBox6,SendBox6) &

 cleanReadBox(NewBox6,ReadBox6,SendBox6,Usr2,NewBox7,ReadBox7,SendBox7) &
 cleanSendBox(NewBox7,ReadBox7,SendBox7,Usr2,NewBox8,ReadBox8,SendBox8) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%SIMULACION1 NOTIPADA%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dec_p_type(simulacion1(mensaje,mensaje,user,user, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla, casilla, casilla,casilla)).
simulacion1(MsgPingRequest,MsgPingReply,User1,User2,NewBoxInit,ReadBoxInit,SendBoxInit,
                                          NewBoxAdd1,ReadBoxAdd1,SendBoxAdd1,NewBoxAdd2,ReadBoxAdd2,SendBoxAdd2,
                                          NewBoxPing1,ReadBoxPing1,SendBoxPing1,NewBoxPing2,ReadBoxPing2,SendBoxPing2,
                                          NewBoxPeek1,ReadBoxPeek1,SendBoxPeek1,NewBoxPeek2,ReadBoxPeek2,SendBoxPeek2,
                                          NewBoxClean1,ReadBoxClean1,SendBoxClean1, NewBoxClean2,ReadBoxClean2,SendBoxClean2):-

    gestorMailsInit(NewBoxInit,ReadBoxInit,SendBoxInit) &
    addUser(NewBoxInit,ReadBoxInit,SendBoxInit,User1,NewBoxAdd1,ReadBoxAdd1,SendBoxAdd1) &
    addUser(NewBoxAdd1,ReadBoxAdd1,SendBoxAdd1,User2,NewBoxAdd2,ReadBoxAdd2,SendBoxAdd2)  &
    User1 neq User2 &
    sendMsg(NewBoxAdd2,ReadBoxAdd2,SendBoxAdd2,User2,User1,MsgPingRequest,NewBoxPing1,ReadBoxPing1,SendBoxPing1) &%"hola soy user1".
    sendMsg(NewBoxPing1,ReadBoxPing1,SendBoxPing1,User1,User2,MsgPingReply,NewBoxPing2,ReadBoxPing2,SendBoxPing2) &%"un gusto user1 soy user2"
    readMsg(NewBoxPing2,ReadBoxPing2,SendBoxPing2,User2,MsgDeUser1aUser2,NewBoxPeek1,ReadBoxPeek1,SendBoxPeek1)&
    
    dec(MsgDeUser1aUser2,mensaje) &
    MsgDeUser1aUser2 = MsgPingRequest &

    readMsg(NewBoxPeek1,ReadBoxPeek1,SendBoxPeek1,User1,MsgDeUser2aUser1,NewBoxPeek2,ReadBoxPeek2,SendBoxPeek2)&
    
    dec(MsgDeUser2aUser1,mensaje) &
    MsgDeUser2aUser1 = MsgPingReply &

    cleanReadBox(NewBoxPeek2,ReadBoxPeek2,SendBoxPeek2,User1,NewBoxClean1,ReadBoxClean1,SendBoxClean1) &
    cleanReadBox(NewBoxClean1,ReadBoxClean1,SendBoxClean1,User2,NewBoxClean2,ReadBoxClean2,SendBoxClean2) .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Teorema 1: AddUser preserva las pfun%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dec_p_type(n_gestorMailsInvPFun(casilla, casilla, casilla)).
n_gestorMailsInvPFun(UsersNewMails,UsersReadMails,UsersSendMails) :-
   neg(
       pfun(UsersNewMails) & 
       pfun(UsersReadMails) &
       pfun(UsersSendMails) ).

:- dec_p_type(gestorMailsInvPFun(casilla, casilla, casilla)).
gestorMailsInvPFun(UsersNewMails,UsersReadMails,UsersSendMails) :-
   pfun(UsersNewMails) & 
   pfun(UsersReadMails) &
   pfun(UsersSendMails).

:- dec_p_type(theoremAddUser1(user, casilla, casilla,casilla, casilla, casilla,casilla)). 
theoremAddUser1(User1,N0,R0,S0,N0_,R0_,S0_) :-
   neg(  (gestorMailsInvPFun(N0,R0,S0) & addUser(N0,R0,S0,User1,N0_,R0_,S0_)) implies  gestorMailsInvPFun(N0_,R0_,S0_) ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Teorema 2: AddUser preserva la igualdad entre los dominios de las casillas%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dec_p_type(n_gestorMailsInvDomEq(casilla, casilla, casilla)).
n_gestorMailsInvDomEq(UsersNewMails,UsersReadMails,UsersSendMails) :-
     dec(NM, set(user)) &
     dec(RM, set(user)) &
     dec(SM, set(user)) & 
     dom(UsersNewMails, NM) &
     dom(UsersReadMails,RM) &
     dom(UsersSendMails,SM) &
     neg(
     NM = RM &
     RM = SM & 
     SM = NM ) .

:- dec_p_type(gestorMailsInvDomEq(casilla, casilla, casilla)).
gestorMailsInvDomEq(UsersNewMails,UsersReadMails,UsersSendMails) :-
     dec(NM, set(user)) &
     dec(RM, set(user)) &
     dec(SM, set(user)) & 
     dom(UsersNewMails, NM) &
     dom(UsersReadMails,RM) &
     dom(UsersSendMails,SM) &
     NM = RM &
     RM = SM & 
     SM = NM .


:- dec_p_type(theoremAddUser2(user, casilla, casilla,casilla, casilla, casilla,casilla)). 
theoremAddUser2(User1,N0,R0,S0,N0_,R0_,S0_) :-
neg( (  gestorMailsInvDomEq(N0,R0,S0) & addUser(N0,R0,S0,User1,N0_,R0_,S0_) ) implies (gestorMailsInvDomEq(N0_,R0_,S0_)) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%EXTRA THEO%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Teorema 3: SendMsg preserva las pfun%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dec_p_type(n_capMaxima(int)).
n_capMaxima(X) :- X < 0 or 2 < X.

:- dec_p_type(theoremSendMsg1(user, user,mensaje,casilla, casilla,casilla, casilla, casilla,casilla)). 
theoremSendMsg1(User1,User2,Msg,N0,R0,S0,N0_,R0_,S0_) :-
   neg((gestorMailsInvPFun(N0,R0,S0) & sendMsg(N0,R0,S0,User2,User1,Msg,N0_,R0_,S0_))  implies  gestorMailsInvPFun(N0_,R0_,S0_) ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Teorema 4: AddUser agrega uniformemente un usuario a las casillas%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dec_p_type(theoremAddUser3PreCondition(user, casilla, casilla,casilla)). 
theoremAddUser3PreCondition(User1,N0,R0,S0) :-
    dec(ND,set(user)) &
    dec(RD,set(user)) &
    dec(SD,set(user)) &
    dom(N0, ND) &
    dom(R0, RD) &
    dom(S0, SD) &
    User1 nin ND &
    User1 nin RD & 
    User1 nin SD .

:- dec_p_type(n_theoremAddUser3PostCondition(user, casilla, casilla,casilla)). 
n_theoremAddUser3PostCondition(User1,N0,R0,S0) :-
    dec(ND,set(user)) &
    dec(RD,set(user)) &
    dec(SD,set(user)) &
    dom(N0, ND) &
    dom(R0, RD) &
    dom(S0, SD) &
    neg(
        User1 in ND &
        User1 in RD &
        User1 in SD).


:- dec_p_type(theoremAddUser3PostCondition(user, casilla, casilla,casilla)). 
theoremAddUser3PostCondition(User1,N0,R0,S0) :-
    dec(ND,set(user)) &
    dec(RD,set(user)) &
    dec(SD,set(user)) &
    dom(N0, ND) &
    dom(R0, RD) &
    dom(S0, SD) &
    User1 in ND &
    User1 in RD &
    User1 in SD.

:- dec_p_type(theoremAddUser3(user, casilla, casilla,casilla, casilla, casilla,casilla)). 
theoremAddUser3(User1,N0,R0,S0,N0_,R0_,S0_) :-
    neg( ( theoremAddUser3PreCondition(User1,N0,R0,S0) & addUser(N0,R0,S0,User1,N0_,R0_,S0_)) implies theoremAddUser3PostCondition(User1,N0_,R0_,S0_) ).




%Es importante que se validen estas propiedades porque sabiendo que se agrega uniformemente usuarios a las casillas y siempre los dominios de las casillas van a ser iguales, sin perder de vista que preserva a las casillas como pfun. Entonce
%a la hora de operar con el envio o recepción de mensajes nos despreocupamos de checkear que los usuarios interviniente estén registrados en todas las casillas, además de evitarnos inconsistencias en
%el modelo como que por ejemplo un usuario solo pueda enviar y otro solo recibir. Todo esto gracias a la validez de los 3 teoremas de AddUser

%Comando: theoremSendMsg1(user:user1,user:user2,"ping",N0,R0,S0,N1,R1,S1) & dec([N0,R0,S0,N1,R1,S1], casilla).
%Comando: theoremAddUser1(user:user1,N0,R0,S0,N1,R1,S1) & dec([N0,R0,S0,N1,R1,S1], casilla).
%Comando: theoremAddUser2(user:user1,N0,R0,S0,N1,R1,S1) & dec([N0,R0,S0,N1,R1,S1], casilla).
%Comando: theoremAddUser3(user:user1,N0,R0,S0,N1,R1,S1) & dec([N0,R0,S0,N1,R1,S1], casilla).
%Comando: simulacion2(user:usr1,user:usr2,{[user:usr1, {[user:usr1,"Borrador"],[user:usr2,"hola usr1"]}] , [user:usr2,{[user:usr1, "chau usr2"]}] }, {[user:usr1,{}],[user:usr2,{}]},{[user:usr2, {[user:usr1,"hola usr1"]}] , [user:usr1,{[user:usr2, "chau usr2"],[user:usr1,"Borrador"]}] },N2,R2,S2,N3,R3,S3,N4,R4,S4,N5,R5,S5,N6,R6,S6,N7,R7,S7,N8,R8,S8) & dec([N2,R2,S2,N3,R3,S3,N4,R4,S4,N5,R5,S5,N6,R6,S6,N7,R7,S7,N8,R8,S8],casilla).
% Comando: dec([N0,R0,S0,N1,R1,S1,N2,R2,S2,N3,R3,S3,N4,R4,S4,N5,R5,S5,N6,R6,S6,N7,R7,S7,N8,R8,S8],casilla) &  simulacion1("mandame hola","hola",user:user1,user:user2,N0,R0,S0,N1,R1,S1,N2,R2,S2,N3,R3,S3,N4,R4,S4,N5,R5,S5,N6,R6,S6,N7,R7,S7,N8,R8,S8) .