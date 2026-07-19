// Especificações:
//
// Uma arena digital organiza partidas de um jogo de esconde-esconde em que jogadores assumem papéis diferentes durante cada rodada. 
// Em uma rodada, cada jogador pode ser classificado como Camuflado ou Caçador, mas nunca pode ocupar os dois papéis ao mesmo tempo.
// Toda rodada deve ter pelo menos um caçador e pelo menos um camuflado. Cada camuflado escolhe exatamente uma área do mapa para se esconder,
// como parede, chão, objeto ou cenário decorativo. 
//
// Cada área do mapa possui uma cor predominante, e o camuflado deve usar uma pintura da mesma cor da área escolhida.
// Um camuflado pode estar sem pose definida enquanto ainda estiver se preparando, mas, ao final da preparação, todo camuflado deve possuir exatamente uma pose.
// Um caçador pode encontrar vários camuflados durante a rodada, mas um camuflado só pode ser encontrado uma única vez.
// Camuflados já encontrados não podem continuar marcados como escondidos.
// A rodada só pode ser considerada finalizada quando todos os camuflados forem encontrados.
//

// Representa um jogador da arena;
// Cada jogador possui uma função durante uma rodada.
sig Jogador {
	papel: set Funcao
}

// Representa a função que um jogador assumirá durante a rodada.
abstract sig Funcao {
}


// Função que será responsável por procurar os camuflados.
sig Cacador extends Funcao {
	encontrados: set Camuflado
}

// Função que será responsável por esconder-se dos caçadores.
sig Camuflado extends Funcao {
	pose: lone Pose,
	preparado: one EstadoPreparo,
	encontrado: one EstadoEncontrado,
	area: one Area,
	cor: one Cor
}

// Pose que um camuflado adotará durante uma rodada.
sig Pose {}

// Estado em que se encontra o camuflado:
// Encontrado caso um caçador o tenha feito;
// Escondido caso nenhum caçador o tenha feito.
abstract sig EstadoEncontrado {}
sig Encontrado, Escondido extends EstadoEncontrado {}

// Estado em que se encontra o camuflado:
// Preparado caso já tenha decidido sua pose;
// NaoPreparado caso ainda não tenha decidido sua pose.
abstract sig EstadoPreparo {}
sig Preparado, NaoPreparado extends EstadoPreparo {}

// Representa uma região onde um camuflado está escondido.
abstract sig Area {
	cor: one Cor
}

sig Parede extends Area {}
sig Chao extends Area {}
sig Objeto extends Area {}
sig CenarioDecorativo extends Area {}

// Cor utilizada pelo camuflado que por consequência
// é a mesma da área em que está escondido.
sig Cor {}

// Representa uma partida do jogo.
sig Rodada {
	acabou: one Terminou,
	cacador: some Cacador,
	camuflado: some Camuflado,
	jogadores: set Jogador
}

// Estado da rodada:
// Sim caso a rodada esteja finalizada;
// Nao caso a rodada ainda esteja em andamento;
abstract sig Terminou {}
sig Sim, Nao extends Terminou {}

-- Rodada

// A quantidade de jogadores deve ser igual à soma
// dos caçadores e camuflados participantes.
fact CardinalidadeRodada {
	all r: Rodada | #(r.cacador + r.camuflado) = #r.jogadores
}

// A rodada somente será considerada encerrada
// quando todos os camuflados tiverem sido encontrados.
fact RodadaAcabaTodosEncontrados {
	all r: Rodada | r.acabou in Sim <=>  (all c: r.camuflado | c.encontrado in Encontrado)
}

// A rodada permanecerá em andamento enquanto ainda
// tiver camuflados escondidos.
fact RodadaNaoAcabaSemEncontrarTodos {
	all r: Rodada, c: r.camuflado | c.encontrado in Escondido implies r.acabou in Nao 
}

-- Jogador

// Todo jogador participando do jogo possui exatamente
// um papel dentro de uma rodada.
fact JogadorNaRodadaTemFuncao {
	all j: Jogador | all r: Rodada |  j in r.jogadores implies (one f: Funcao | f in j.papel and f in (r.cacador + r.camuflado))
}

// Todo camuflado com o estado de Encontrado
// deve ter sido encontrado por um caçador.
fact CamufladoEncontradoPorCacador {
	all cm: Camuflado  | cm.encontrado in Encontrado implies (one cd: Cacador |  cm in cd.encontrados)
}

// Todo camuflado que foi encontrado por um caçador
// deve possuir o estado de Encontrado.
fact CamufladoEncontradoNaoFicaEscondido {
	all cd: Cacador | all cm: cd.encontrados | cm.encontrado in Encontrado
}

// Um caçador só pode encontrar um camuflado que
// esteja na mesma rodada que a dele.
fact CacadorSoEncontraCamufladoDaRodada {
	all r: Rodada | all cd: r.cacador | all cm: cd.encontrados | cm in r.camuflado
}

// Um caçador só pode encontrar um camuflado que
// esteja no estado de Preparado.
fact SoEncotradoPreparado {
	all c: Camuflado | c.encontrado in Encontrado implies c.preparado in Preparado
}

// Um jogador não pode participar de duas rodadas em andamento
// ao mesmo tempo.
fact JogadorSoParticipaDeUmaRodadaSimultanea {
	all j: Jogador | lone r: Rodada | j in r.jogadores and r.acabou in Nao
}

-- Cor

// A cor de todo camuflado deve ser a mesma que a
// cor da área onde o mesmo se encontra.
fact CamufladoPintaCorArea {
	all c: Camuflado | all a: Area | a = c.area implies c.cor = a.cor
}

-- Pose

// Todo camuflado preparado necessariamente deve
// possuir exatamente uma pose.
fact PreparadoTemPose {
	all c: Camuflado | c.preparado in Preparado implies #c.pose = 1
}

-- Evitar Avulsos

// Evita que funções de Caçador e Camuflado não
// estejam associadas a nenhum jogador.
fact SemFuncaoSolta {
	all f:Funcao | one r: Rodada |one j: Jogador | f in (r.cacador + r.camuflado) and f in j.papel
}

// Evita que estados de Encontrado e NaoEncontrado
// estejam associadas a nenhum jogador camuflado.
fact SemEstadoEncontradoAvulso {
	all e: EstadoEncontrado | one c: Camuflado | e = c.encontrado
}

// Evita que cores estejam associadas a nenhuma área.
fact SemCorAvulsa {
	all c:Cor | one a: Area | c = a.cor
}

// Evita que estados de Preparado e NaoPreparado
// estejam associadas a nenhum jogador camuflado.
fact SemPreparoAvulso {
	all p: EstadoPreparo | one c: Camuflado | p = c.preparado
}

// Evita que poses estejam associadas a nenhum jogador camuflado.
fact SemPoseAvulsa {
	all p: Pose | one c: Camuflado | p = c.pose
}

// Evita que estados de Terminou (Sim e Nao) estejam
// associadas a nenhuma rodada.
fact SemAcabouAvulso {
	all t: Terminou | one r: Rodada | t = r.acabou
}

run {#Rodada = 3} for 20
