from tkinter import *
from tkinter import messagebox

import time
import pygame
import pygame_menu
import numpy as np
import itertools
import sys
import networkx as netx
import collections
import requests
from pygame import gfxdraw

# Constants of the game
API_URL = 'http://localhost:3000'
BOARD_COLOR = (193, 117, 8)
BOARD_WIDTH = 800
BOARD_BORDER = 70
STONE_RADIUS = 30
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)
TURN_POS = (10, 20)
SCORE_POS = (BOARD_BORDER + 30, BOARD_WIDTH - BOARD_BORDER + 20)
DOT_RADIUS = 4
BOARD_SIZE = 6


def make_grid(size):
    # Returns a list that defines the gridlines using (start_point, end_point) pairs, receives as argument the size of
    # the grid and returns a tuple which allows to have an ordered and unchangeable grid with the format:
    # Tuple[List[Tuple[float,float]]] that indicates start and end points of gridlines

    start_points = []
    end_points = []

    # linespace returns an array with evenly spaced numbers over an interval
    # First argument, takes the value of the border, since we are drawing inside the board as starting value
    # Second argument, takes the whole board and removes the value of the border so we get the end value
    # Third argument, divides the board in the number of spaces indicated in the size

    # full, when given a single number as first argument returns an array full of the value given in the second argument
    # ej. full(5,2) = array([5,5]) full(2,5)=([2,2,2,2,2])

    # list(zip()) converts two 1D arrays into a single 2D array, zipping them inside a list

    # vertical start points y
    xs = np.linspace(BOARD_BORDER, BOARD_WIDTH - BOARD_BORDER, size)
    ys = np.full(size, BOARD_BORDER)
    start_points = start_points + list(zip(xs, ys))

    # horizontal start points x
    xs = np.full(size, BOARD_BORDER)
    ys = np.linspace(BOARD_BORDER, BOARD_WIDTH - BOARD_BORDER, size)
    start_points = start_points + list(zip(xs, ys))

    # vertical end points y
    xs = np.linspace(BOARD_BORDER, BOARD_WIDTH - BOARD_BORDER, size)
    ys = np.full(size, BOARD_WIDTH - BOARD_BORDER)
    end_points += list(zip(xs, ys))

    # horizontal end points x
    xs = np.full(size, BOARD_WIDTH - BOARD_BORDER)
    ys = np.linspace(BOARD_BORDER, BOARD_WIDTH - BOARD_BORDER, size)
    end_points += list(zip(xs, ys))

    return start_points, end_points


def xy_to_colrow(x, y, size):
    # Conversion of coordinates x,y to column and row number, receives
    # x - x position, y - y position, size of grid
    # Returns a tuple of ints containing numbers of intersection

    # Create a constant(unit) that indicates the inner space without borders divided in the size of the board -1
    # this gives us an unit that indicates in which one of the columns and/or rows a certain x or y is located
    # then we find said place using the distance to the border(less the actual border) divided in the unit and round

    unit = (BOARD_WIDTH - (2 * BOARD_BORDER)) / (size - 1)
    x_dist = x - BOARD_BORDER
    y_dist = y - BOARD_BORDER
    col = int(round(x_dist / unit))
    row = int(round(y_dist / unit))
    return col, row


def colrow_to_xy(col, row, size):
    # Conversion of rows and columns to x,y coordinates using
    # col - column number, row - row number, size of grid
    # Returns a tuple of floats containing the coordinates of intersection
    # Same process as above but in reverse
    unit = (BOARD_WIDTH - 2 * BOARD_BORDER) / (size - 1)
    x = int(BOARD_BORDER + col * unit)
    y = int(BOARD_BORDER + row * unit)
    return x, y


def is_valid_move(col, row, board, black_turn):
    # To check if placing a stone of a certain color is valid on the current board state
    # col - column number, row -row number, board a grid that contains the size * size of the matrix inside
    # Returns true if valid otherwise false
    # First it checks if somehow the column number is lesser than 0 (which should not happen but it breaks the system)
    # Then it compares the column is bigger or equal than the total size of the board (no plays out of bounds)
    # Does the same for the rows, if none of that is true, returns true only if the space of the move on the
    # board is empty (0) if not, then returns false for the space is already occupied

    # Evalua que no se salga de los margenes
    if col < 0 or col >= board.shape[0]:
        return False
    if row < 0 or row >= board.shape[0]:
        return False
    return board[col, row] == 0  # Retorna True si esta libre


def is_suicide(col, row, board, prisoners, black_turn):
    self_color = "black" if black_turn else "white"
    other_color = "white" if black_turn else "black"

    aux_board = board.copy()
    aux_board[col, row] = 1 if black_turn else 2

    isCapture, return_board, aux_prisoners = is_capture(
        aux_board, prisoners, self_color, other_color)
    if isCapture:
        # Si hace captura no es un suicidio
        return False, return_board, aux_prisoners
    else:
        group = get_group(col, row, aux_board, self_color)
        if has_no_liberties(aux_board, group):
            # Si no captura y queda sin libertades significa que es un suicidio
            return True, board, prisoners
        else:
            # Si no captura pero queda con libertades entonces pongo la piedra
            return False, aux_board, prisoners


def is_capture(board, prisoners, self_color, other_color):
    capture = False
    for group in list(get_groups(board, other_color)):
        if has_no_liberties(board, group):
            capture = True
            for x, y in group:
                board[x, y] = 0
            prisoners[self_color] += len(group)
    return capture, board, prisoners


def get_group(col, row, board, self_color):
    for group in get_groups(board, self_color):
        if (col, row) in group:
            return group


def get_groups(board, color):
    # Retrieve stone groups of a certain color on a certain board state
    # board - a grid that contains the total size and the size of the matrix inside
    # color name of the color to get the groups for
    # returns a list of col-row pairs, each defining a group as a list of touples with the format
    # List[List[Tuple[int, int]]]
    # Creates a size variable with the size of the board
    # Adds a color code so black is 1 and white is 2
    # Gets all the coordinates where stones from color are placed
    # Creates a graph with the size of the board
    # Creates a set of stones using the coordinates from the selected color
    # Creates a two dimension set that contains combinations of the range-1 arguments as coupled numbers
    # ej. set(itertools.product(range(2), range(2))) = {(0, 1), (1, 0), (1, 1), (0, 0)}
    # Identifies the stones to remove by identifying the spaces that the stones of the current color are not using
    # Uses the identified spaces to delete said nodes from the generated graph
    # Returns a series of sets of nodes that represent the different groups found

    size = board.shape[0]
    if color == "black":
        color_code = 1
    else:
        color_code = 2

    xs, ys = np.where(board == color_code)
    graph = netx.grid_graph(dim=[size, size])
    stones = set(zip(xs, ys))
    all_spaces = set(itertools.product(range(size), range(size)))
    stones_to_remove = all_spaces - stones
    graph.remove_nodes_from(stones_to_remove)
    return netx.connected_components(graph)


def has_no_liberties(board, group):
    # Checks if the given group has liberties on a given board
    # board, the object board which contains the size and the matrix of contents
    # group, list of couple col,row pairs that define a certain stone group in the List[Tuple[int, int]] format
    # returns a boolean with true if liberties are found, otherwise returns false
    # For every stone in the group that is represented as an x,y set of coordinates checks for every space in the
    # four cardinal directions, if any of the is empty(0) then the group has a liberty hence ir returns false
    # If the cardinal search does not find an empty space then the group has no liberties

    for x, y in group:
        if x > 0 and board[x - 1, y] == 0:
            return False
        if y > 0 and board[x, y - 1] == 0:
            return False
        if x < board.shape[0] - 1 and board[x + 1, y] == 0:
            return False
        if y < board.shape[0] - 1 and board[x, y + 1] == 0:
            return False
    return True


# MODOS: 1 vs 1, 1 vs Machine, Machine vs Machine*********
# Pasamos profundidad y turno
# Profundidad inicia en 5 al buscar

def heuristica(board, prisoners):
    # La heuristica va a ser la cantidad de mis fichas prisioneras
    #  menos las prisionera del otro por 7 (para tener un rango).

    # Tambien se tendran en cuenta la cantidad de fichas en peligro
    #  tanto las mias como las del rival, que se saca multiplica por 3

    # Y los espacios dominados tanto por mi como por el rival
    #  que se multiplica por 5

    # Heuristica de cada nodo (momento en el tablero)
    # (+) 7 por diferencia de fichas capturadas
    # (-) 3 por diferencia de fichas en peligro (1 sola libertad)
    # (+) 5 por diferencia de espacios dominados

    # Los primeros 3 movimientos ya vienen precargados, con la intención de
    #  no analizar un numero demasiado grande de jugadas, ganando eficiencia

    # Piensa 4 jugadas adelante
    # No piensa si ya no hay espacios

    # Si una jugada es ilegal no la revisa, es ilegal cuando:
    #  el espacio esta ocupado o ocuando es un suicidio

    prisoners_black = prisoners['black']
    prisoners_white = prisoners['white']

    groups_black = get_groups(board, 'black')
    groups_white = get_groups(board, 'white')

    dangerous_black = 0
    dangerous_white = 0

    for group in list(groups_black):
        dangerous_black += quantityDangerous(board, group)

    for group in list(groups_white):
        dangerous_white += quantityDangerous(board, group)

    spaces_black, spaces_white = dominated_spaces(board)

    diff_prisoners = prisoners_black - prisoners_white
    diff_dangerous = (dangerous_black * -1) - (dangerous_white * -1)
    diff_spaces = spaces_black - spaces_white
    return (diff_prisoners * 7) + (diff_dangerous * 3) + (diff_spaces * 5)


# Esto es mi minmax con poda alfa beta
def get_best_movement(board_node, prisoners, black_turn, depth, alpha, beta):

    if depth == 0:  # Tengo que pensar en un nodo terminal, tal vez board lleno
        x, y, node_board, node_prisioners = board_node
        return x, y, heuristica(node_board, node_prisioners)

    if black_turn:  # Maximizador
        maxEva = -9999999
        max_X = None
        max_Y = None
        for child in get_child_nodes(board_node[2], prisoners, black_turn):
            x, y, aux_board, aux_prisoners = child
            evaX, evaY, eva = get_best_movement(
                child, aux_prisoners, not black_turn,  depth - 1, alpha, beta)
            if eva > maxEva:
                maxEva = eva
                max_X = x
                max_Y = y

            # Agregando poda alfa beta
            if maxEva >= beta:
                return (max_X, max_Y, maxEva)

            if maxEva > alpha:
                alpha = maxEva

        return max_X, max_Y, maxEva

    else:  # Minimizador
        minEva = +9999999
        min_X = None
        min_Y = None
        for child in get_child_nodes(board_node[2], prisoners, black_turn):
            x, y, aux_board, aux_prisoners = child
            evaX, evaY, eva = get_best_movement(
                child, aux_prisoners, not black_turn, depth - 1, alpha, beta)
            if eva < minEva:
                minEva = eva
                min_X = x
                min_Y = y

            # Agregando poda alfa beta
            if minEva <= alpha:
                return (min_X, min_Y, minEva)

            if minEva < beta:
                beta = minEva

        return min_X, min_Y, minEva


# Acá voy a hacer magia
def get_child_nodes(board, prisoners, black_turn):
    # print(board)
    nodes = []
    # 6 porque es el actual tamaño del tablero (6x6)
    for x in range(BOARD_SIZE):
        for y in range(BOARD_SIZE):
            if board[x, y] == 0:  # Si el espacio esta libre
                isSuicide, return_board, return_prisoners = is_suicide(
                    x, y, board, prisoners.copy(), black_turn)
                if not isSuicide:
                    content = (x, y, return_board, return_prisoners)
                    nodes.append(content)  # Agrego solo tableros posibles
    return nodes


def quantityDangerous(board, group):
    # Verificar las fichas que tenemos en peligro
    # es decir las de las cadenas que tengan 1 sola libertad
    liberties = 0
    for x, y in group:
        # Revisamos los laterales de cada una de las fichas
        if x > 0 and board[x - 1, y] == 0:
            liberties += 1
        if y > 0 and board[x, y - 1] == 0:
            liberties += 1
        if x < board.shape[0] - 1 and board[x + 1, y] == 0:
            liberties += 1
        if y < board.shape[0] - 1 and board[x, y + 1] == 0:
            liberties += 1

    # Si tienen mas de una libertad retornamos 0 (indicando que no hay unidades en peligro)
    if liberties > 1:
        return 0
    else:  # Si tienen 1 sola libertad significa que estan en peligro la totalidad del grupo
        return len(group)


def dominated_spaces(board):
    # 1 para Negras, 2 para Blancas

    # Verificar los espacios dominados
    #  son dominados si tienen mas fichas al rededor de un color que de otro
    spaces_blacks = 0
    spaces_whites = 0

    # 6 porque es el actual tamaño del tablero (6x6)
    for x in range(BOARD_SIZE):
        for y in range(BOARD_SIZE):
            if (board[x, y] == 0):  # Espacios no ocupados
                around_blacks = 0
                around_whites = 0
                # Revisamos los laterales de cada una de las fichas
                #  por si encontramos una ficha negra a su alrededor
                if x > 0 and board[x - 1, y] == 1:
                    around_blacks += 1
                if y > 0 and board[x, y - 1] == 1:
                    around_blacks += 1
                if x < board.shape[0] - 1 and board[x + 1, y] == 1:
                    around_blacks += 1
                if y < board.shape[0] - 1 and board[x, y + 1] == 1:
                    around_blacks += 1

                # Revisamos los laterales de cada una de las fichas
                #  por si encontramos una ficha blanca a su alrededor
                if x > 0 and board[x - 1, y] == 2:
                    around_whites += 1
                if y > 0 and board[x, y - 1] == 2:
                    around_whites += 1
                if x < board.shape[0] - 1 and board[x + 1, y] == 2:
                    around_whites += 1
                if y < board.shape[0] - 1 and board[x, y + 1] == 2:
                    around_whites += 1

                # Verificamos y sumamos si es que un espacio es dominado
                if around_blacks > around_whites:
                    spaces_blacks += 1
                elif around_whites > around_blacks:
                    spaces_whites += 1

    return spaces_blacks, spaces_whites


def init_pygame():
    # Starts the game screen using the default size from WIDTH
    pygame.init()
    start_menu()


def init_game(args):
    screen, mode = args
    game = Game(size=BOARD_SIZE, screen=screen, mode=mode)
    game.clear_screen()
    game.draw()
    while True:
        game.update()
        if mode < 4:
            pygame.time.wait(100)
        else:
            pygame.time.wait(2000)


def start_menu():
    screen = pygame.display.set_mode((BOARD_WIDTH, BOARD_WIDTH))
    menu = pygame_menu.Menu('Principal Menu', 500, 400,
                            theme=pygame_menu.themes.THEME_BLUE)
    menu.add.button('Play Human vs Human', init_game, (screen, 1))
    menu.add.button('Play Human vs Machine', init_game, (screen, 2))
    menu.add.button('Play Machine vs Machine', init_game, (screen, 3))
    menu.add.button('Play Online (Black)', init_game, (screen, 5))
    menu.add.button('Play Online (White)', init_game, (screen, 4))
    menu.add.button('Quit', pygame_menu.events.EXIT)
    menu.mainloop(screen)


class Game:
    def __init__(self, size, screen, mode):
        # start of the game, creates an array full of 0s that will be the starting board
        # starts the turn with the black player
        # creates a collection that creates any item that will be accessed, as long as they are not present already
        # assigns the value of the start/end points from the edges of the newly created grid using the input size
        self.screen = screen
        self.font = pygame.font.SysFont("arial", 30)
        self.board = np.zeros((size, size))
        self.size = size
        self.black_turn = True
        self.prisoners = collections.defaultdict(int)
        self.start_points, self.end_points = make_grid(self.size)
        self.pass_counter = 0
        self.turn = 0
        self.depth = 3  # (Solo impares) No recomiendo subir la profundidad
        self.mode = mode
        self.last_x_machine = 3
        self.last_y_machine = 3
        self.score = 0
        if mode == 3:
            self.init_movements()

    def init_movements(self):
        self.board[2, 2] = 1
        self.board[2, 3] = 1
        self.board[3, 2] = 2
        self.board[3, 3] = 2
        self.draw()

    def clear_screen(self):
        # fill board with color defined and draw the lines inside using the star and end points
        self.screen.fill(BOARD_COLOR)
        for start_point, end_point in zip(self.start_points, self.end_points):
            pygame.draw.line(self.screen, BLACK, start_point, end_point)

        # add guide dots
        guide_dots = [3, self.size // 2, self.size - 4]
        for col, row in itertools.product(guide_dots, guide_dots):
            x, y = colrow_to_xy(col, row, self.size)
            gfxdraw.aacircle(self.screen, x, y, DOT_RADIUS, BLACK)
            gfxdraw.filled_circle(self.screen, x, y, DOT_RADIUS, BLACK)

        # Update the game screen after the lines and dots have been drawn
        pygame.display.flip()

    def change_turn(self):
        self.black_turn = not self.black_turn
        self.draw()
        self.turn += 1

    def pass_move(self):
        # Pass the turn to the other player
        self.pass_counter += 1
        self.black_turn = not self.black_turn
        self.draw()

    def best_movement(self, last_x, last_y):
        print("Buscando mejor jugada para ",
              'negras' if self.black_turn else 'blancas', ' asi que calma')
        start = time.time()
        qx, qy, heuristica_value = get_best_movement(
            (last_x, last_y, self.board), self.prisoners, self.black_turn, self.depth, -9999999, +999999)  # Esto es lo nuevo
        end = time.time()
        print('Evaluation time: {}s'.format(round(end - start, 7)))
        print('Recommended move: X = {}, Y = {}'.format(qx, qy))
        print('Valor heuristica: ', heuristica_value)
        # Si no encuentra un movimiento valido posible entonces acaba la partida y busca al ganador
        if (qx == None or qy == None):
            self.getWinner()
            sys.exit()
        self.score = heuristica_value
        self.draw()
        return qx, qy

    def play_machine(self, last_x, last_y):
        x, y = self.best_movement(last_x, last_y)
        self.board[x, y] = 1 if self.black_turn else 2
        self_color = "black" if self.black_turn else "white"
        other_color = "white" if self.black_turn else "black"

        # Revisa si se realizó una captura para actualizar el tablero
        isCapture, return_board, aux_prisoners = is_capture(
            self.board, self.prisoners, self_color, other_color)

        return (x, y)

    # Es la funcion principal
    def play(self):
        # LA JUGADA DE ELLOS NO ESTA COMIENDO FICHAS (YA), REVISAR, EVITAR LOOP INFINITO DE CAPTURAS(PENDIENTE) -> puede ser acabando la partida
        # get board position and check for valid clicks INSIDE the actual board

        # JUGADA QUE LLEGA DEL OTRO JUGADOR (DISTRIBUIDO)
        if self.mode == 4:
            response = requests.get(API_URL + '/getTurn').json()
            print('Respuesta: ', response)
            print(self.black_turn)
            if response['black_turn'] == self.black_turn:
                x, y = response['position_x'], response['position_y']
                print(x, y)
                isSuicide, return_board, return_prisoners = is_suicide(
                    x, y, self.board, self.prisoners, self.black_turn)
                self.board = return_board
                self.prisoners = return_prisoners
                self.score = response['score']
                self.change_turn()
                self.mode = 5
                self.draw()

        # JUGADA USUARIO
        elif self.mode == 1 or self.mode == 2 or self.mode == 5:
            x, y = pygame.mouse.get_pos()
            col, row = xy_to_colrow(x, y, self.size)
            if not is_valid_move(col, row, self.board, self.black_turn):
                Tk().wm_withdraw()
                messagebox.showwarning('Warning', 'Invalid movement')
                return
            else:
                # Evalua que no sea un suicidio, en caso de que no, hace la jugada
                isSuicide, return_board, return_prisoners = is_suicide(
                    col, row, self.board, self.prisoners, self.black_turn)
                if isSuicide:
                    Tk().wm_withdraw()
                    messagebox.showwarning('Warning', 'This is a suicide')
                    return
                self.board = return_board
                self.prisoners = return_prisoners
                self.score = heuristica(self.board, self.prisoners)
                if self.mode == 5:
                    requests.post(url=API_URL + '/postTurn', json={
                        'black_turn': self.black_turn,
                        'position_x': col,
                        'position_y': row,
                        'score': self.score
                    }).json()
                    self.mode = 4
                    self.change_turn()
                    self.draw()
                

        # Si una persona jugó significa que no pasa turno
        if self.mode == 1:
            self.pass_counter = 0
            self.change_turn()
        # Turno de la maquina
        elif self.mode == 2:
            self.change_turn()
            self.play_machine(x, y)
            self.change_turn()
        # Turno de la maquina
        elif self.mode == 3:
            self.last_x_machine, self.last_y_machine = self.play_machine(
                self.last_x_machine, self.last_y_machine)
            self.change_turn()
        self.score = heuristica(self.board, self.prisoners)

    def draw(self):
        # draw stones - filled circle and antialiased ring
        self.clear_screen()
        for col, row in zip(*np.where(self.board == 1)):
            x, y = colrow_to_xy(col, row, self.size)
            gfxdraw.aacircle(self.screen, x, y, STONE_RADIUS, BLACK)
            gfxdraw.filled_circle(self.screen, x, y, STONE_RADIUS, BLACK)
        for col, row in zip(*np.where(self.board == 2)):
            x, y = colrow_to_xy(col, row, self.size)
            gfxdraw.aacircle(self.screen, x, y, STONE_RADIUS, WHITE)
            gfxdraw.filled_circle(self.screen, x, y, STONE_RADIUS, WHITE)

        # text for score and turn info
        score_msg = (
            f"Black's ☠: {self.prisoners['black']}"
            + f"     White's ☠: {self.prisoners['white']}"
            + f"     Score: {self.score}"
        )
        txt = self.font.render(score_msg, True, BLACK)
        self.screen.blit(txt, SCORE_POS)
        turn_msg = (
            f"{'Black' if self.black_turn else 'White'} to move. "
            + "Click to place stone, press P to pass."
        )
        txt = self.font.render(turn_msg, True, BLACK)
        self.screen.blit(txt, TURN_POS)
        pygame.display.flip()
        pygame.display.update()

    def getRockInBoard(self):
        quantityBlacks = 0
        quantityWhites = 0
        for i in range(self.size):
            for j in range(self.size):
                if self.board[i, j] == 1:
                    quantityBlacks += 1
                elif self.board[i, j] == 1:
                    quantityWhites += 1
        return quantityBlacks, quantityWhites

    def getWinner(self):
        qBlacks, qWhites = self.getRockInBoard()
        Tk().wm_withdraw()
        messagebox.showinfo('Info', f"Black's Rocks: {qBlacks}\n"
                                    f"Black's Prisoners: {self.prisoners['black']}\n"
                                    f"White's Rocks: {qWhites}\n"
                                    f"White's Prisoners: {self.prisoners['white']}\n"
                                    f"SCORE: {self.score}")
        winner = "Black" if self.score > 0 else "White "
        messagebox.showinfo('Winner', "The winner is: " + winner)

    def update(self):
        # TODO: button that undoes the last action
        # Si no juega sola la maquina entonces tomo en cuenta los clicks
        if self.mode == 1 or self.mode == 2 or self.mode == 5:
            events = pygame.event.get()
            for event in events:
                if event.type == pygame.MOUSEBUTTONUP:
                    self.play()
                if event.type == pygame.QUIT:
                    sys.exit()
                if event.type == pygame.KEYUP:
                    if event.key == pygame.K_p:
                        if self.pass_counter == 1:
                            # Finish the game
                            self.getWinner()
                            sys.exit()
                        self.pass_move()
        elif self.mode == 3 or self.mode == 4:
            self.play()


if __name__ == "__main__":
    init_pygame()
