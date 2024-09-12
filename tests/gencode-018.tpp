{Se, Repita, Função}

inteiro: n

inteiro fatorial(inteiro: n)
    inteiro: ret,fat
    se n > 0 então {não calcula se n > 0}
        fat := 1
        repita
            fat := fat * n
            n := n - 1
        até n = 0
        ret := fat {retorna o valor do fatorial de n}
    senão
        ret := 0
    fim
    retorna(ret)
fim

inteiro principal()
    inteiro: fat
    leia(n)
    fat := fatorial(n)
    escreva(fat)
    retorna(0)
fim
