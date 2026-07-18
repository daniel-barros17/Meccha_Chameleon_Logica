sig Jogador {
	papel: set Funcao
}

abstract sig Funcao {
}


sig Cacador extends Funcao {
	encontrados: set Camuflado
}

sig Camuflado extends Funcao {
	pose: lone Pose,
	preparado: one EstadoPreparo,
	encontrado: one EstadoEncontrado,
	area: one Area,
	cor: one Cor
}

sig Pose {}

abstract sig EstadoEncontrado {}
sig Encontrado, Escondido extends EstadoEncontrado {}

abstract sig EstadoPreparo {}
sig Preparado, NaoPreparado extends EstadoPreparo {}

abstract sig Area {
	cor: one Cor
}

sig Parede extends Area {}
sig Chao extends Area {}
sig Objeto extends Area {}
sig CenarioDecorativo extends Area {}

sig Cor {}

sig Rodada {
	acabou: one Terminou,
	cacador: some Cacador,
	camuflado: some Camuflado,
	jogadores: set Jogador
}

abstract sig Terminou {}
sig Sim, Nao extends Terminou {}

-- Rodada

fact CardinalidadeRodada {
	all r: Rodada | #(r.cacador + r.camuflado) = #r.jogadores
}

fact RodadaAcabaTodosEncontrados {
	all r: Rodada | r.acabou in Sim <=>  (all c: r.camuflado | c.encontrado in Encontrado)
}

fact RodadaNaoAcabaSemEncontrarTodos {
	all r: Rodada, c: r.camuflado | c.encontrado in Escondido implies r.acabou in Nao 
}

-- Jogador
fact JogadorNaRodadaTemFuncao {
	all j: Jogador | all r: Rodada |  j in r.jogadores implies (one f: Funcao | f in j.papel and f in (r.cacador + r.camuflado))
}

fact CamufladoEncontradoPorCacador {
	all cm: Camuflado  | cm.encontrado in Encontrado implies (one cd: Cacador |  cm in cd.encontrados)
}

fact CamufladoEncontradoNaoFicaEscondido {
	all cd: Cacador | all cm: cd.encontrados | cm.encontrado in Encontrado
}

fact CacadorSoEncontraCamufladoDaRodada {
	all r: Rodada | all cd: r.cacador | all cm: cd.encontrados | cm in r.camuflado
}

fact SoEncotradoPreparado {
	all c: Camuflado | c.encontrado in Encontrado implies c.preparado in Preparado
}

fact JogadorSoParticipaDeUmaRodadaSimultanea {
	all j: Jogador | lone r: Rodada | j in r.jogadores and r.acabou in Nao
}


-- Cor

fact CamufladoPintaCorArea {
	all c: Camuflado | all a: Area | a = c.area implies c.cor = a.cor
}

-- Pose
fact PreparadoTemPose {
	all c: Camuflado | c.preparado in Preparado implies #c.pose = 1
}

-- Evitar Avulsos

fact SemFuncaoSolta {
	all f:Funcao | one r: Rodada |one j: Jogador | f in (r.cacador + r.camuflado) and f in j.papel
}

fact SemEstadoEncontradoAvulso {
	all e: EstadoEncontrado | one c: Camuflado | e = c.encontrado
}

fact SemCorAvulsa {
	all c:Cor | one a: Area | c = a.cor
}

fact SemPreparoAvulso {
	all p: EstadoPreparo | one c: Camuflado | p = c.preparado
}

fact SemPoseAvulsa {
	all p: Pose | one c: Camuflado | p = c.pose
}

fact SemAcabouAvulso {
	all t: Terminou | one r: Rodada | t = r.acabou
}

run {#Rodada = 3} for 20
