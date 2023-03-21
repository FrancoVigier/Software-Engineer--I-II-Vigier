-cargar la setloglib.slog
-mail.pl es el modelo en {log} con sus simulaciones y teoremas tipados
-mailsft.tex es el modelo en fastest para realizar los casos de prueba
-mailzeves.tex es el modelo en zeves con sus teoremas y pruebas
-el tex del informe esta en una carpeta porque el tex esta dividido en secciones 
y tiene subdirectorios

Project of specification of a mail manager in Z, testing its invariants with universal quantifiers in Z-Eves (theorem proving) and performing model checking on the Z model. We also performed real automatic testing with Fastest (functional testing).

Briefly, the problem to be represented is a simple mail manager. Each user has a place in the mailboxes of this manager which provides main operations such as sending, receiving and reading messages, as well as adding users to the manager and emptying the mailboxes for a specific user. Every member of the mail manager has three message boxes, numbering them: the new box, the read box and the received box.
To increase the difficulty, we want the mailboxes of each user to be limited in terms of message capacity (axiomatically).
