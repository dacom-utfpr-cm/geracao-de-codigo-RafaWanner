import sys
import os
import subprocess
import json
import re

from sys import argv, exit

import logging

logging.basicConfig(
     level = logging.DEBUG,
     filename = "sema.log",
     filemode = "w",
     format = "%(filename)10s:%(lineno)4d:%(message)s"
)
log = logging.getLogger()

import ply.yacc as yacc

from tppparser import main as tppparser_main

# Get the token map from the lexer.  This is required.
from tpplex import tokens

from mytree import MyNode
from anytree.exporter import DotExporter, UniqueDotExporter
from anytree import Node, RenderTree, AsciiStyle

from myerror import MyError

error_handler = MyError('SemaErrors')
syn = MyError('ParserErrors')
le = MyError('LexerErrors')

checkKey = False
checkTpp = False

errorArray = []
warningArray = []

root = None



#    def find_node(node, target_name):
#        if node.name == target_name:
#            return node
#        for child in getattr(node, 'children', []):
#            result = find_node(child, target_name)
#            if result:
#                return result
#        return None
#
#    # Search for the 'principal' function declaration in the tree
#    principal_node = find_node(root, 'principal')
#    
#    if principal_node is None:
#        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-MAIN-NOT-DECL'))

#    def find_all_nodes(node, target_name, result=None):
#        if result is None:
#            result = []
#        if node.name == target_name:
#            result.append(node)
#        for child in getattr(node, 'children', []):
#            find_all_nodes(child, target_name, result)
#        return result
#
#    # Usage
#    principal_nodes = find_all_nodes(root, 'principal')
#    if not principal_nodes:
#        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-MAIN-NOT-DECL'))



# Funcoes Basicas

def walk_tree(node, path):
    """Walk the tree following the given path of node names and return the final node."""
    current_node = node
    for name in path:
        current_node = next((child for child in current_node.children if child.name == name), None)
        if current_node is None:
            return None
    return current_node

def check_node_exists(node, error_code):
    """Check if node exists, otherwise report an error."""
    if (not node):
        errorArray.append(error_handler.newError(checkKey, error_code))
        return False
    return True

def find_all_nodes(node, target_name, result=None):
    if result is None:
        result = []
    if node.name == target_name:
        result.append(node)
    for child in getattr(node, 'children', []):
        find_all_nodes(child, target_name, result)
    return result

def find_all_paths(node, path):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        temp_result = walk_tree(a[i], temp_path)

        if (temp_result is not None):
            result.append(temp_result)

    return result

def find_all_paths_excludint_parent(node, path, parent):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        if (find_parent_node(a[i], parent) is None):
            temp_result = walk_tree(a[i], temp_path)

            if (temp_result is not None):
                result.append(temp_result)

    return result

def find_all_paths_including_parent(node, path, parent):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        if (find_parent_node(a[i], parent) is not None):
            temp_result = walk_tree(a[i], temp_path)

            if (temp_result is not None):
                result.append(temp_result)

    return result

def find_all_paths_including_parent_excludint_parent(node, path, parent_in, parent_out):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        if (find_parent_node(a[i], parent_in) is not None and find_parent_node(a[i], parent_out) is None):
            temp_result = walk_tree(a[i], temp_path)

            if (temp_result is not None):
                result.append(temp_result)

    return result

def find_all_nodes_children(node, path):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        temp_result = walk_tree(a[i], temp_path)

        if (temp_result is not None):
            for child in getattr(temp_result, 'children', []):
                result.append(child)

    return result

def find_parent_node(start_node, target_name):
    """Walk up the tree from the start_node searching for a node with the target_name and return that node."""
    current_node = start_node
    
    while current_node is not None:
        if current_node.name == target_name:
            return current_node
        current_node = current_node.parent  # Move up to the parent node

    return None  # Return None if the target node is not found

def find_all_nodes_children_with_parent(node, path, parent):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        temp_result = walk_tree(a[i], temp_path)

        if (temp_result is not None):
            if (find_parent_node(temp_result, parent) is not None):
                for child in getattr(temp_result, 'children', []):
                    result.append(child)

    return result

def find_all_nodes_children_with_parent_without_parent(node, path, parent_in, parent_out):
    temp_path = path[1:]
    result = []
    temp_result = None

    a = find_all_nodes(node, path[0])

    for i in range(len(a)):
        temp_result = walk_tree(a[i], temp_path)

        if (temp_result is not None):
            if (find_parent_node(temp_result, parent_in) is not None and find_parent_node(temp_result, parent_out) is None):
                for child in getattr(temp_result, 'children', []):
                    result.append(child)

    return result

def get_string_after_last_underscore(s):
    match = re.search(r'_(?!.*_)(.*)', s)
    if match:
        return match.group(1)
    return s  # Return the whole string if no underscore is found

def comparator_type(root, node, type_coparasion, error_msg=None, warning_msg=None, var_dec_check=False):
    call_var = node

    variable_path = [
        "lista_variaveis",
        "var",
        "ID",
        call_var.name
    ]

    lista_parametros_path = [
        "lista_parametros",
        "parametro", 
        "id",
        call_var.name
    ]

    pai = find_parent_node(call_var, "cabecalho")
    variable = None
    variable_type = None
    variable_not_dec = False

    if (find_all_paths_including_parent(pai, variable_path, "declaracao_variaveis")):
        """Variable Declared On Function"""
        variable = find_all_paths_including_parent(pai, variable_path, "declaracao_variaveis")

        variable_type = find_parent_node(variable[0], "declaracao_variaveis").children[0].children[0].name

    elif (find_all_paths(pai, lista_parametros_path)):
        """Variable Declared On Function Parameters"""
        variable = find_all_paths(pai, lista_parametros_path)
        
        variable_type = find_parent_node(variable[0], "parametro").children[0].children[0].name

    elif (find_all_paths_including_parent_excludint_parent(root, variable_path, "declaracao_variaveis", "cabecalho")):
        """Variable Declared Globaly"""
        variable = find_all_paths_including_parent_excludint_parent(root, variable_path, "declaracao_variaveis", "cabecalho")

        variable_type = find_parent_node(variable[0], "declaracao_variaveis").children[0].children[0].name

    else:
        """Variable Not Declared Treat As Null"""
        variable_not_dec = True

    if (variable_type != type_coparasion):
            if (var_dec_check and variable_not_dec):
                errorArray.append(error_handler.newError(checkKey, "ERR-SEM-VAR-NOT-DECL"))
            if (error_msg):
                errorArray.append(error_handler.newError(checkKey, error_msg))
            elif (warning_msg):
                warningArray.append(error_handler.newError(checkKey, warning_msg))
            return False
    else:
        return True



# Executor
def execute_order_66(root):
    s_funcao_principal(root) # Feita
    s_declaracao_de_funcao(root) # Feita
    s_retorno_de_funcao(root) # Feita

    s_variavel_nao_declarada(root) # Feita
    s_variavel_declarada_inicializada_utilizada(root) # Feita



# ---Funções e Procedimentos---

# checa se ha funcao principal
def s_funcao_principal(root):
    # Ensure the root node is "programa"
    if not check_node_exists(root if root.name == "programa" else None, 'ERR-SEM-MAIN-NOT-DECL'):
        return

    # Define the path for the function we're looking for
    path_to_main = [
        "lista_declaracoes", 
        "declaracao", 
        "declaracao_funcao", 
        "cabecalho", 
        "ID", 
        "principal"
    ]
    
    # Walk the tree based on the predefined path
    node_principal = find_all_paths(root, path_to_main)

    # Check if we found the main function node ("principal")
    if not check_node_exists(node_principal, 'ERR-SEM-MAIN-NOT-DECL'):
        return

# checa se a funcao foi declarada antes de ser chamada
def s_declaracao_de_funcao(root):
    function_path = [
        "chamada_funcao",
        "ID"
    ]

    cabecalho_path = [
        "declaracao",
        "declaracao_funcao",
        "cabecalho",
        "ID"
    ]

    function_calls = find_all_nodes_children(root, function_path)
    dec_funcs = find_all_nodes_children(root, cabecalho_path)
    dec_temp = []

    for i in range(len(dec_funcs)):
        if (dec_funcs[i].name == "principal"):
            dec_temp.append(dec_funcs[i])

    for i in range(len(dec_temp)):
        dec_funcs.remove(dec_temp[i])

    for function_call in function_calls:
        dec_temp = []

        for i in range(len(dec_funcs)):
            if (function_call.name == dec_funcs[i].name):
                dec_temp.append(dec_funcs[i])

        for i in range(len(dec_temp)):
            dec_funcs.remove(dec_temp[i])

        function_is_declared = False
        function_node = find_parent_node(function_call, "lista_declaracoes")

        if (function_call.name == "principal"):
            func_temp = walk_tree(function_node, cabecalho_path).children[0]
            if (func_temp):
                if (func_temp.name == "principal"):
                    warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-CALL-REC-FUNC-MAIN'))
                    continue
            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-CALL-FUNC-MAIN-NOT-ALLOWED'))
            continue
        
        while function_node:
            function_check = walk_tree(function_node, cabecalho_path)

            if function_check and function_check.children[0].name == function_call.name:
                function_is_declared = True
                s_identificador_de_funcao(function_check.children[0], function_call)
                break
            else:
                function_node = walk_tree(function_node, ["lista_declaracoes"])
        
        if not function_is_declared:
            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-CALL-FUNC-NOT-DECL'))

    for i in range(len(dec_funcs)):
        warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-FUNC-DECL-NOT-USED'))

# checa se a quantidade de parametros reais e formais de uma funcao sao iguais
def s_identificador_de_funcao(node_formal, node_real):
    parameters_path = [
        "lista_parametros",
        "parametro"
    ]

    argumentos_path = [
        "lista_argumentos",
        "expressao"
    ]

    formal_length = find_all_paths(node_formal.parent.parent, parameters_path)
    real_length = find_all_paths(node_real.parent.parent, argumentos_path)

    if (len(real_length) > len(formal_length)):
        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-CALL-FUNC-WITH-MANY-ARGS'))

    elif (len(real_length) < len(formal_length)):
        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-CALL-FUNC-WITH-FEW-ARGS'))

    else:
        s_verifica_tipagem_chamada_de_funcao(root, formal_length, real_length)

# checa se a funcao foi retornada corretamente
def s_retorno_de_funcao(root):
    retorno_path = [
        "cabecalho",
        "corpo",
        "acao",
        "retorna"
    ]

    dec_func = find_all_nodes(root, "declaracao_funcao")
    retorno_var = None

    for i in range(len(dec_func)):
        retorno = walk_tree(dec_func[i], retorno_path)
        function_type = dec_func[i].children[0].children[0].name

        if (retorno is not None):
            # checa se o retorno e uma variavel
            retorno_check = find_all_nodes_children_with_parent(retorno, ["fator", "var", "ID"], "expressao")

            if (retorno_check):
                for j in range(len(retorno_check)):
                    retorno_var = retorno_check[j]
                    comparator_type(root, retorno_var, function_type, error_msg='ERR-SEM-FUNC-RET-TYPE-ERROR', var_dec_check=True)

            else:
                retorno_check = find_all_nodes_children_with_parent(retorno, ["fator", "numero"], "expressao")
                if (retorno_check):
                    for j in range(len(retorno_check)):
                        retorno_var = get_string_after_last_underscore(retorno_check[j].name)
                        if (retorno_var != function_type):
                            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-FUNC-RET-TYPE-ERROR'))

        else:
            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-FUNC-RET-TYPE-ERROR'))



# ---Variaveis---

# verifica se a variavel foi escrita sem ser declarada
def s_variavel_nao_declarada(root):
    atribuicao_path = [
        "atribuicao",
        "var",
        "ID"
    ]

    atribuicoes = find_all_nodes_children(root, atribuicao_path)

    for i in range(len(atribuicoes)):
        pai = find_parent_node(atribuicoes[i], "cabecalho")
        if (pai == None):
            pai = root

        variable_path = [
            "lista_variaveis",
            "var",
            "ID",
            atribuicoes[i].name
        ]

        variables = find_all_paths_including_parent(pai, variable_path, "declaracao_variaveis")
        if (not variables and pai != root):
            variables = find_all_paths_including_parent(root, variable_path, "declaracao_variaveis")

        if (not variables):
            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-VAR-NOT-DECL'))

# verifica se a variavel foi declarada, utilizada e inicializada
def s_variavel_declarada_inicializada_utilizada(root):
    variable_path = [ 
        "lista_variaveis", 
        "var", 
        "ID"
    ]

    variables = find_all_nodes_children_with_parent(root, variable_path, "declaracao_variaveis")

    for i in range(len(variables)):
        pai = find_parent_node(variables[i], "cabecalho")
        if (pai == None):
            pai = root
            
            # checa se possui mais de uma declaracao da msm variavel
            if (find_parent_node(variables[i], "lista_declaracoes").children[0].name == "lista_declaracoes"):
                if (find_all_nodes(find_parent_node(variables[i], "lista_declaracoes").children[0], variables[i].name)):
                    warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-VAR-DECL-PREV'))
                    continue

        else:
            if (find_parent_node(variables[i], "corpo").children[0].name == "corpo"):
                if (find_all_nodes(find_parent_node(variables[i], "corpo").children[0], variables[i].name)):
                    warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-VAR-DECL-PREV'))
                    continue

        variable_check_path = [
            "declaracao_variaveis", 
            "lista_variaveis", 
            "var", 
            "ID",
            variables[i].name
        ]

        atribuicao_path = [
            "atribuicao",
            "var",
            "ID",
            variables[i].name
        ]

        expression_path = [
            "fator",
            "var",
            "ID",
            variables[i].name
        ]

        atribuicoes = find_all_paths(pai, atribuicao_path)

        # verifica se a atribuicao esta condizente com o escopo
        if (pai == root):
            for j in range (len(atribuicoes)):
                if (find_parent_node(atribuicoes[j], "cabecalho")):
                    if (find_all_paths(find_parent_node(atribuicoes[j], "cabecalho"), variable_check_path)):
                        atribuicoes.remove(atribuicoes[j])
        
        expresions = find_all_paths_including_parent(pai, expression_path, "expressao")

        # verifica se a expressao usada esta condizente com o escopo
        if (pai == root):
            for j in range (len(expresions)):
                if (find_parent_node(expresions[j], "cabecalho")):
                    if (find_all_paths(find_parent_node(expresions[j], "cabecalho"), variable_check_path)):
                        expresions.remove(expresions[j])

        #print(variables[i].name)
        #print(atribuicoes)
        #print(expresions)

        if (len(variables[i].parent.parent.children) > 1):
            if (variables[i].parent.parent.children[1].name == "indice"):
                s_indice_nao_inteiro(variables[i].parent.parent.children[1])
                
        if (atribuicoes):
            for j in range(len(atribuicoes)):
                if (len(atribuicoes[j].parent.parent.children) > 1):
                    if (atribuicoes[j].parent.parent.children[1].name == "indice"):
                        if(not s_indice_nao_inteiro(atribuicoes[j].parent.parent.children[1])):
                            atribuicoes.remove(atribuicoes[j])
                else:
                    s_verifica_tipagem_atribuicao_variavel(root, find_parent_node(variables[i], "declaracao_variaveis"), atribuicoes[j].parent.parent.parent)

        if (expresions):
            for k in range(len(expresions)):
                if (len(expresions[k].parent.parent.children) > 1):
                    if (expresions[k].parent.parent.children[1].name == "indice"):
                        if(not s_indice_nao_inteiro(expresions[k].parent.parent.children[1])):
                            expresions.remove(expresions[k])
                else:
                    s_verifica_tipagem_uso_variavel(root, variables[i].parent.parent.parent.parent, find_parent_node(expresions[k], "atribuicao"))

        #print(variables[i].name)
        #print(atribuicoes)
        #print(expresions)

        # verifica se a variavel foi inicializada e ou utilizada
        if not atribuicoes:
            if not expresions:
                warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-VAR-DECL-NOT-USED'))
            
            else:
                warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-VAR-DECL-NOT-INIT'))

        elif not expresions:
            warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-VAR-DECL-INIT-NOT-USED'))



# ---Atribuição de tipos distintos e Coerções implícitas---

# verifica se a atribuicao da variavel corresponde a tipagem
def s_verifica_tipagem_atribuicao_variavel(root, dec_node, atr_node):
    num_path = [
        "fator",
        "numero"
    ]

    var_path = [
        "fator",
        "var",
        "ID"
    ]

    func_path = [
        "fator",
        "chamada_funcao"
    ]

    dec_node_type = dec_node.children[0].children[0]

    atr_node_nums = find_all_nodes_children_with_parent_without_parent(atr_node, num_path, "expressao", "chamada_funcao")

    atr_node_vars = find_all_nodes_children_with_parent_without_parent(atr_node, var_path, "expressao", "chamada_funcao")

    # vai dar errado se tiver funcao dentro de funcao
    atr_node_funcs = find_all_paths_including_parent(atr_node, func_path, "expressao")

    if (atr_node_nums and atr_node_vars):
        for i in range (len(atr_node_nums)):
            num_type = get_string_after_last_underscore(atr_node_nums[i].name)
            if (num_type != dec_node_type.name):
                 for j in range (len(atr_node_vars)):
                    if (not comparator_type(root, atr_node_vars[j], dec_node_type.name, warning_msg="WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-EXP", var_dec_check=True)):
                        return "f_exp"
    
    if (atr_node_nums and atr_node_funcs):
        for j in range (len(atr_node_nums)):
            num_type = get_string_after_last_underscore(atr_node_nums[j].name)
            if (num_type != dec_node_type.name):
                for i in range (len(atr_node_funcs)):
                    dec_func_path = [
                        "cabecalho",
                        "ID",
                        atr_node_funcs[i].children[0].children[0].name
                    ]

                    dec_func_type_path = [
                        "tipo",
                        dec_node_type.name
                    ]

                    dec_func = find_all_paths_including_parent(root, dec_func_path, "declaracao_funcao")
                    if (not walk_tree(dec_func[0].parent.parent.parent, dec_func_type_path)):
                        warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-EXP'))
                        return "f_exp"

    if (atr_node_funcs and atr_node_vars):
        for i in range (len(atr_node_funcs)):
            dec_func_path = [
                "cabecalho",
                "ID",
                atr_node_funcs[i].children[0].children[0].name
            ]

            dec_func_type_path = [
                "tipo",
                dec_node_type.name
            ]

            dec_func = find_all_paths_including_parent(root, dec_func_path, "declaracao_funcao")
            if (not walk_tree(dec_func[0].parent.parent.parent, dec_func_type_path)):
                for j in range (len(atr_node_vars)):
                    if (not comparator_type(root, atr_node_vars[j], dec_node_type.name, warning_msg="WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-EXP", var_dec_check=True)):
                        return "f_var"

    if (atr_node_nums):
        for i in range (len(atr_node_nums)):
            num_type = get_string_after_last_underscore(atr_node_nums[i].name)
            if (num_type != dec_node_type.name):
                #print(dec_node_type.name)
                warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-NUM'))
                return "f_num"

    if (atr_node_vars):
        for i in range (len(atr_node_vars)):
            if (not comparator_type(root, atr_node_vars[i], dec_node_type.name, warning_msg="WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-VAR", var_dec_check=True)):
                return "f_var"

    if (atr_node_funcs):
        for i in range (len(atr_node_funcs)):
            dec_func_path = [
                "cabecalho",
                "ID",
                atr_node_funcs[i].children[0].children[0].name
            ]

            dec_func_type_path = [
                "tipo",
                dec_node_type.name
            ]

            dec_func = find_all_paths_including_parent(root, dec_func_path, "declaracao_funcao")
            if (not walk_tree(dec_func[0].parent.parent.parent, dec_func_type_path)):
                warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-RET-VAL'))
                return "f_func"

# verifica se o uso da variavel corresponde a tipagem
def s_verifica_tipagem_uso_variavel(root, dec_node, exp_node):
    try:
        dec_node_type = dec_node.children[0].children[0]

        exp_node_var = exp_node.children[0].children[0].children[0]

        if (exp_node_var):
            if (not comparator_type(root, exp_node_var, dec_node_type.name, var_dec_check=True)):
                return "f_var"
    except:
        return

# verifica se a tipagem dos parametros formais e reais sao iguais
def s_verifica_tipagem_chamada_de_funcao(root, nodes_formal, nodes_real):
    parameter_real_path = [
        "expressao_logica",
        "expressao_simples",
        "expressao_aditiva",
        "expressao_multiplicativa",
        "expressao_unaria",
        "fator"
    ]

    for i in range(len(nodes_formal)):
        parameter_real = find_all_nodes_children(nodes_real[i], parameter_real_path)
        formal_type = nodes_formal[i].children[0].children[0].name

        if (parameter_real[0].name != "var"):
            real_type = get_string_after_last_underscore(parameter_real[0].children[0].name)

            if (real_type != formal_type):
                warningArray.append(error_handler.newError(checkKey, 'WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-FUNC-ARG'))

        else:
            call_var = parameter_real[0].children[0].children[0]
            comparator_type(root, call_var, formal_type, warning_msg='WAR-SEM-ATR-DIFF-TYPES-IMP-COERC-OF-FUNC-ARG')



# ---Aranjos---

# verifica se o indice do array e um inteiro
def s_indice_nao_inteiro(root):
    indice_path = [
        "indice", 
        "expressao", 
        "expressao_logica", 
        "expressao_simples",
        "expressao_aditiva",
        "expressao_multiplicativa",
        "expressao_unaria",
        "fator",
        "numero"
    ]

    indice = find_all_nodes_children(root, indice_path)

    for i in range(len(indice)):
        if (indice[i].name) != "NUM_INTEIRO":
            errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-ARRAY-INDEX-NOT-INT'))
            return False
        
    return True



# Programa Principal.
def main(args):
    global checkKey
    global checkTpp
    global errorArray
    global warningArray

    if(len(args) < 2):
        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-USE'))
        raise TypeError(error_handler.newError(checkKey, 'ERR-SEM-USE'))

    posArgv = 0

    for idx,arg in enumerate(args):
        aux = arg.split('.')
        if aux[-1] == 'tpp':
            checkTpp = True
            posArgv = idx
        
        if arg == "-k":
            checkKey = True
    
    if checkKey and len(args) < 3:
        errorArray.append(le.newError(checkKey, 'ERR-SEM-USE'))
        raise TypeError(errorArray)
    elif not checkTpp:
        errorArray.append(le.newError(checkKey, 'ERR-SEM-NOT-TPP'))
        raise IOError(errorArray)
    elif not os.path.exists(argv[posArgv]):
        errorArray.append(le.newError(checkKey, 'ERR-SEM-FILE-NOT-EXISTS'))
        raise IOError(errorArray)
    else:
        root = tppparser_main(args)
        execute_order_66(root)

        # To visualize the tree:
        #for pre, fill, node in RenderTree(root):
        #    print(f"{pre}{node.name}")

    #print (errorArray)
    #print (warningArray)

    if len(errorArray) > 0:
        if len(warningArray) > 0:
            errorArray += warningArray
        #print (errorArray)
        raise IOError(errorArray)
    
    else:
        return root, warningArray

if __name__ == "__main__": 
    try:
        main(sys.argv)
    except Exception as e:
        print('\n--------------------------------------------- ERR-SEM ---------------------------------------------\n')
        for x in range(len(e.args[0])):
            print (e.args[0][x])
    except (ValueError, TypeError):
        print('\n-------------------------------------------------------------------------------------------\n')
        for x in range(len(e.args[0])):
            print (e.args[0][x])