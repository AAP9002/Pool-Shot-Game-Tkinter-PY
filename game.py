""" COMP16321 Coursework 2
Alan Anthony Prophett - Last Modified 25 November 2022

screen size 1600 x 900

Pool game with 2 game modes (levels and co-op), made with tkinter
- user can save and load level completion progress
- user can pause same while balls are moving
- 2 users can play co-op with automatic scoring and penalty system
- leader board showing xp earned from level games

ball physics conserve momentum and velocity
- work out direction of balls after collision
- work out energy transfer based on amount of contact on collision
- affected with friction by table and collisions

controls
- Move mouse over table to ain
- SPACE to shoot

cheats
- [default] i (change pocket size)
- [default] w (instant win)(in co-op, one ball must be potted first due to colour:player allocation)

boss key
- [default] Control key + B (display windows desktop image)

pause in game
- [default] p (pause/resume game) or use pause on screen button
"""
#imports
from tkinter import Tk, Canvas, Label, Button, PhotoImage, StringVar, IntVar, Radiobutton, Text
#from random import randint as rand # used for testing
from math import atan2,cos,sin,pi,sqrt
from datetime import datetime, timedelta
from json import dump, load

# window properties
window = Tk()
WINDOW_WIDTH = 1600
WINDOW_HEIGHT = 900
GAME_TITLE = "Pool Shots"
BG_COLOR = '#EADEDA'
SIDE_BAR_X_OFFSET = 0
SIDE_BAR_Y_OFFSET = 0
TEXT_COLOR = '#E9E3E6'
PRIMARY_BUTTON_COLOR = '#6BFFB8'
RHS_BACKGROUND = '#780206'
LHS_BACKGROUND = '#061161'
MID_BACKGROUND = '#5F051A'
SIDE_BAR_WIDTH=200
MENU_BUTTON_WIDTH = 150

# set table and ball to scale (6ft x 3ft table)
BALL_RAD = 15
TABLE_LENGTH = 1080
TABLE_WIDTH = 540
TABLE_X_OFFSET = 315
TABLE_Y_OFFSET = 170
YELLOW_COLOR = '#FFD400'
QUE_BALL_COLOR = '#FFFFFF'
RED_COLOR = '#d90368'
BLACK_BALL_COLOR="#000000"
TABLE_COLOR='#6A8E7F'
POCKET_SIZE =40


# constant collision values
WALL_COLLISION_ENERGY_LOSS = 0.95
TABLE_BALL_FRICTION = 0.99
BALL_COLLISION_ENERGY_LOSS = 0.95
VELOCITY_TO_MOVEMENT_SCALE =20

# frequently used lambda functions
# solve for distance between 2 points
distance_between_2_points = lambda x1,y1,x2,y2: sqrt((x1-x2)**2+(y1-y2)**2)
 # get direction from starting point to end point in radians
direction_between_2_points = lambda from_x, from_y,to_x, to_y: atan2((to_y-from_y),(to_x-from_x))
# solve direction based on velocity
x_y_velocity_to_direction = lambda vx,vy: direction_between_2_points(0,0,vx,vy)
# solve object overall velocity using x velocity and y velocity
x_y_velocity_single_velocity = lambda vx,vy: distance_between_2_points(0,0,vx,vy)
# modules which can return negative values, as % only returns the absolute value
improved_mod = lambda n, base : n - int(n/base) * base
# get the difference between 2 directions
get_difference_in_angles = lambda base_l , line: atan2(sin(base_l-line), cos(base_l-line))

#pre load images
WINDOW_BG_IMAGE = PhotoImage(file = "./background_gradient.png")
BOSS_KEY_IMAGE = PhotoImage(file="./boss_key_image.png")
COMPLETED_LEVEL_IMAGE = PhotoImage(file="./Level_buttons/COMPLETED_LEVEL_ICON.png")
LEVEL_1_BUTTON = PhotoImage(file="./Level_buttons/L1.png")
LEVEL_2_BUTTON = PhotoImage(file="./Level_buttons/L2.png")
LEVEL_3_BUTTON = PhotoImage(file="./Level_buttons/L3.png")
LEVEL_4_BUTTON = PhotoImage(file="./Level_buttons/L4.png")
LEVEL_5_BUTTON = PhotoImage(file="./Level_buttons/L5.png")
LEVEL_6_BUTTON = PhotoImage(file="./Level_buttons/L6.png")
LEVEL_7_BUTTON = PhotoImage(file="./Level_buttons/L7.png")
LEVEL_8_BUTTON = PhotoImage(file="./Level_buttons/L8.png")
INSTRUCTIONS_IMAGE = PhotoImage(file="./instructions.png")

# accounts
current_account_id = IntVar()
current_account_id.set(-1)
current_user_selected_username = StringVar()
current_user_selected_username.set("Not Selected")
new_user_input_initials_box = Text()
all_accounts = {}

# pool table
table = Canvas(window)
balls = []
pots = [[0,0],
[TABLE_LENGTH/2,-10],
[TABLE_LENGTH,0],
[0,TABLE_WIDTH],
[TABLE_LENGTH/2,TABLE_WIDTH+10],
[TABLE_LENGTH,TABLE_WIDTH]]
pockets = []

# in game scoring and checks
yellow_Score = 0
red_Score = 0
aim_guide_line = None
aim_line_Of_Impact_Angle = 0
in_game = False
ball_in_motion = False
Current_Selected_Level = IntVar()

# overlay variables
top_Status_bar = StringVar()
secondary_description = StringVar()
#set background of window
announcement_Label = Label(window,
                        font=("Helvetica",40,'bold'),
                        background="white")
paused_game = False
paused_game_button = Button()
pause_button_text = StringVar()
announcement_text_overlay = StringVar()
announcement_text_overlay = ""
back_to_menu_button = Button()
retry_button = Button()

# in game
current_game_title = ""
current_game_description = ""
current_game_is_co_op = False
current_game_score_text = StringVar()
current_game_waiting_for_shot = True
increase_pocket_size_on = False

# level specific in game
current_level_selected = IntVar()
current_level_playing=0
current_game_xp_worth = 0
current_game_shot_limit_left_text = StringVar()
current_game_time_limit_left_text = StringVar()
current_game_shot_limit_left = -1
current_game_time_limit_left = -1
current_game_yellow_ball_target = 0
current_game_red_ball_target = 0
current_game_end_time = datetime.today()

# co-op specific in game
current_game_player_1_turn = True
current_game_color_turn_to_go = ""
current_game_foul_penalty = 0
current_game_yellow_potted_in_last_round = False
current_game_red_potted_in_last_round = False
turn_announcer = StringVar()

# misc variables and initial states
temp_widgets = [] # holds temp widget ids to be destroyed on change of screen
Label(window, image=WINDOW_BG_IMAGE).place(x=-2,y=-2)#set background of window
welcome_Label_text = "Welcome"
show_boss_key_image = False
boss_key_overlay = Label(window, image=BOSS_KEY_IMAGE)
instructions_display = Label(window, image=INSTRUCTIONS_IMAGE)
select_Level_buttons = [Button()]*8
instructions_showing = False
user_settings = {}
setting_options = []
ball_config_file_name = "Standard"
instructions_button = Button()

####################################################################################################
############################################# Ball OBJECT ##########################################
####################################################################################################
class ball:
    """BALL object
    - defining ball properties
    - movement logic
    - ball properties and conditions
    - update ball on canvas """
    #define ball variables
    drawn_Object = None
    position_x = None
    position_y = None
    velocity_x = 0
    velocity_y = 0
    color = None
    potted = False
    influence_velocity_x = 0
    influence_velocity_y = 0

    def __init__(self,x,y,color):
        """create new instance of ball
        - create ball to draw on canvas
        - place in initial position
        - set object values for later use"""
        global table
         #create object for canvas
        ball_obj = table.create_oval(x-BALL_RAD,
                                    y-BALL_RAD,
                                    x+BALL_RAD,
                                    y+BALL_RAD,
                                    fill=color)
        self.drawn_Object = ball_obj
        self.color=color
        ## TESTING - uncomment to make all balls move at once
        #self.velocity_x = rand(-200,200)
        #self.velocity_y = rand(-200,200)
        self.position_x = x
        self.position_y = y

    def move(self):
        """move ball based on x and y velocities"""
        if self.potted: # ignore if ball potted
            return
        #scale to convert inches/second to match refresh rate
        move_x = self.velocity_x/VELOCITY_TO_MOVEMENT_SCALE
        move_y = self.velocity_y/VELOCITY_TO_MOVEMENT_SCALE
        self.position_x = self.position_x+ move_x# set new position
        self.position_y = self.position_y+ move_y
        table.move(self.drawn_Object, move_x, move_y ) # move ball on canvas
        self.velocity_x = self.velocity_x *TABLE_BALL_FRICTION # show down by friction
        self.velocity_y = self.velocity_y *TABLE_BALL_FRICTION

    def check_wall_collision(self):
        """Wall collision checker - reverse direction by negating plane velocity"""
        x ,y,vx,vy= self.position_x,self.position_y,self.velocity_x, self.velocity_y

        # left and right cushion
        if((x<=15 and vx<0) or ((x>= TABLE_LENGTH - 15)and vx>0)):
            vx = vx*WALL_COLLISION_ENERGY_LOSS
            vx = - vx # turn around

        # top and bottom cushion
        if((y<=15 and vy<0) or (y>= TABLE_WIDTH - 15 and vy>0)):
            vy = vy*WALL_COLLISION_ENERGY_LOSS
            vy = -vy # turn around

        self.velocity_x, self.velocity_y = vx, vy

    def move_Logic(self):
        """ Checks before movement and move actions """
        if self.potted: # skip if potted
            return
        #check if ball stationary,then check if velocity would overcome 15
        if self.check_if_momentum():
            # if velocity slow enough it wouldn't overcome friction
            if abs(self.velocity_x) < 15 and abs(self.velocity_y) < 15:
                self.velocity_x = 0
                self.velocity_y = 0
            self.check_wall_collision()
            self.move()

    def set_velocity_direction(self,velocity, direction):
        """ set initial velocities of ball

        parameters
        ----------
        velocity - float
            speed of ball
        direction - float
            direction of ball in radians
        """
        # convert from velocity and direction to velocity in x and y plane
        self.velocity_x = velocity*cos(direction)
        self.velocity_y = velocity*sin(direction)

    def influence_velocity_direction(self,velocity, direction):
        """affect on ball due to collision
        solves the resolving x and y velocities

        parameters
        ----------
        velocity - float
            speed of ball
        direction - float
            direction of ball in radians
        """
        # convert from velocity and direction to velocity in x and y plane
        self.influence_velocity_x = velocity*cos(direction)
        self.influence_velocity_y = velocity*sin(direction)

    def apply_influence(self):
        """Apply the influencing x and y velocities"""
        # get resolving x and y velocity, and take away for loss through rebound
        self.velocity_x += self.influence_velocity_x*BALL_COLLISION_ENERGY_LOSS
        self.velocity_y += self.influence_velocity_y*BALL_COLLISION_ENERGY_LOSS
        self.influence_velocity_x = 0
        self.influence_velocity_y = 0

    def set_potted(self):
        """ Once potted, change ball state and color of ball
         (to exclude from future collision checks) """
        global table
        # change ball state to potted
        self.potted = True
        self.velocity_x = 0
        self.velocity_y = 0
        table.itemconfig(self.drawn_Object,fill="gray")

        game_Behavior_Ball_Potted(self.color) # check for game actions after ball potted

    def reset_que_ball(self):
        """Reset que ball to original state"""
        self.potted = False
        self.position_x = 280
        self.position_y = 280
        self.velocity_x = self.velocity_y = 0
        #move to starting position
        table.moveto(self.drawn_Object,self.position_x-BALL_RAD,self.position_y-BALL_RAD)
        table.itemconfig(self.drawn_Object,fill=QUE_BALL_COLOR)# colour white

    def check_if_momentum(self):
        """ check of ball stationary

        Returns
        -------
        bool - True if stationary, False if still moving if in x or y
        """
        #check if moving in any direction
        return (abs(self.velocity_x) > 0) or (abs(self.velocity_y) > 0)

####################################################################################################
############################################# Base Game ############################################
####################################################################################################

def new_game_set_up():
    """ reset game variables and state to a new game """
    global table
    global balls
    global starting_positions
    global yellow_Score
    global red_Score
    global in_game
    global current_game_player_turn
    global current_game_color_turn_to_go
    global current_game_foul_penalty
    global current_game_player_1_turn
    global current_game_waiting_for_shot
    #clear window widgets
    table.delete('all')
    hide_menu_elements()
    # rebind inputs
    table.bind('<Motion>', mouse_move_change_targeting_line)
    #initialise variable
    balls = []
    starting_positions=[]
    yellow_Score = 0
    red_Score = 0
    current_game_foul_penalty = 0
    #add initial objects back onto table
    add_pockets_to_table()
    add_balls_Set_limits_and_game_data()
    add_que()
    in_game = True
    if paused_game: # unpause game
        pause_game()
    # initialise game turn indicators
    current_game_player_turn = 1
    current_game_color_turn_to_go = ""
    current_game_player_1_turn = True
    current_game_waiting_for_shot = True
    if current_game_is_co_op: # in in 2 player mode
        turn_announcer.set("Player 1 you start, break the balls")

def add_pockets_to_table(size=POCKET_SIZE):
    """ Add pockets to table to draw on table

    Parameters
    ----------
    size - float
        set the size of the pockets
        DEFAULT POCKET_SIZE but can be changed for cheat codes"""
    global current_game_pocket_size
    global pockets

    current_game_pocket_size = size
    for pot in pockets: # remove old pockets
        table.delete(pot)
    pockets = []
    for pot in pots: # add pockets, and size
        pockets.append(table.create_oval(
                            pot[0]-size,
                            pot[1]-size,
                            pot[0]+size,
                            pot[1]+size,
                            fill='#000000'))

def add_balls_Set_limits_and_game_data():
    """ Load game config from files, to set level/game up

    Create balls and add them to table
    - get ball position and color config from file
    - create new instances

    Get game data from file
    - time and shots limits
    - game description
    - game title
    - winning scores
    - starting scores
    - xp of level"""
    global balls
    global current_game_shot_limit_left
    global current_game_time_limit_left
    global current_game_title
    global current_game_description
    global current_game_score_text
    global red_Score
    global yellow_Score
    global current_game_red_ball_target
    global current_game_yellow_ball_target
    global current_game_end_time
    global current_game_xp_worth

    starting_positions = []

    # load ball positions from file
    f = open("./BALL_CONFIG/"+ball_config_file_name+".txt")
    #game attributes from config file
    current_game_title = f.readline().strip()
    current_game_description = f.readline().strip()
    current_game_shot_limit_left = int(f.readline().strip())
    current_game_time_limit_left = int(f.readline().strip())
    red_Score = int(f.readline().strip())
    yellow_Score = int(f.readline().strip())
    current_game_red_ball_target = int(f.readline().strip())
    current_game_yellow_ball_target = int(f.readline().strip())
    current_game_xp_worth = int(f.readline().strip())
    # parse ball starting positions
    for line in f.readlines():
        values = line.strip().split(',')
        starting_positions.append([int(values[0]),int(values[1]),int(values[2])])
    f.close()

    # create new ball instances based on properties
    for x in range (len(starting_positions)):
        balls_position = starting_positions[x]
        color = QUE_BALL_COLOR
        if balls_position[2] ==1 :
            color = QUE_BALL_COLOR
        if balls_position[2]  ==2 :
            color = BLACK_BALL_COLOR
        elif balls_position[2] ==3 :
            color = YELLOW_COLOR
        elif balls_position[2] ==4 :
            color = RED_COLOR
        new_ball= ball(x=balls_position[0],y=balls_position[1],color=color)
        balls.append(new_ball)

    #set title and description
    top_Status_bar.set(current_game_title)
    secondary_description.set(current_game_description)
    if current_game_time_limit_left >0:
        current_game_end_time = datetime.today() + timedelta(seconds=current_game_time_limit_left)

def add_que():
    """ initialise Que targeting line """
    global aim_guide_line
    aim_guide_line = table.create_line(balls[0].position_x,balls[0].position_y,700,280, dash=(5,1))


def ball_collision():
    """ Ball to Ball collision physics
    - check for ball collisions
    - calculate directions and velocities after collision
    - distribute velocity depending on the contact on target ball based on line of impact """
    global balls
    for outer_ball in balls: # motion ball
        #get motion ball properties
        x = outer_ball.position_x
        y = outer_ball.position_y
        outer_ball_direction = x_y_velocity_to_direction(vx=outer_ball.velocity_x,
                                                        vy=outer_ball.velocity_y)
        outer_ball_velocity = x_y_velocity_single_velocity(vx=outer_ball.velocity_x,
                                                        vy=outer_ball.velocity_y)
        if outer_ball.potted: # ignore if potted
            continue
        for ball in balls: # check other balls for collision
            if outer_ball is ball: # if the same ball as motion ball
                continue
            if ball.potted: # ignore balls already potted
                continue
            if outer_ball.check_if_momentum(): # check if motion ball is moving
                bx = ball.position_x
                by = ball.position_y
                # if motion ball touching other ball
                if distance_between_2_points(x,y,bx,by) < ((BALL_RAD*2+5)):
                    #line between colliding ball midpoints
                    line_of_action = direction_between_2_points(from_x= x,from_y=y,to_x=bx,to_y=by)
                    # solve motion ball resolving angle,
                    # and ratio of power divided for conservation of energy
                    # <0 when loa+90, >0 when loa-90
                    motion_ball_new_direction = line_of_action

                    #get difference in line of impact and line of action
                    LOA_angle_with_Motion = get_difference_in_angles(base_l=outer_ball_direction,
                                                                    line=line_of_action)

                    if abs(LOA_angle_with_Motion) >(pi/2):
                        # no contact resolving in collision
                        continue
                    # work out motion ball deflection angle
                    if LOA_angle_with_Motion< 0:
                        motion_ball_new_direction -=pi/2
                    if LOA_angle_with_Motion >= 0:
                        motion_ball_new_direction +=pi/2

                    # find angle between line of impact (LOI )and line of action (LOA)
                    # distribute velocity between motion and target ball based on LOI and LOA
                    # conservation of energy and motion
                    velocity_kept_by_motion_BALL = abs(LOA_angle_with_Motion)/(pi/2)

                    motion_ball_new_v = (outer_ball_velocity*velocity_kept_by_motion_BALL)
                    target_ball_new_v = outer_ball_velocity*(1-velocity_kept_by_motion_BALL)

                    #take velocity away from motion ball
                    outer_ball.velocity_x = 0
                    outer_ball.velocity_y = 0
                    outer_ball.influence_velocity_direction(velocity=motion_ball_new_v,
                                                            direction=motion_ball_new_direction)
                    outer_ball.apply_influence()

                    # set influence on target ball,
                    # but do not apply until all collisions have been calculated
                    ball.influence_velocity_direction(velocity=target_ball_new_v,
                                                    direction=line_of_action)
    # Apply target balls new influencing velocities
    for ball in balls:
        ball.apply_influence()


def pot_collision():
    """ check if ball potted
    - if in pot, set ball to potted"""
    global balls
    # go through each ball to check if in a pot
    for ball in balls:
        if ball.potted:
            continue
        x = ball.position_x
        y = ball.position_y
        #check all pockets
        for pot in pots:
            px = pot[0]
            py = pot[1]
            #check if ball in the pocket
            if distance_between_2_points(x,y,px,py)<=current_game_pocket_size:
                ball.set_potted()

def end_current_game():
    """Remove all objects on board and change state to game not running"""
    global table
    global in_game
    global red_Score
    global yellow_Score
#    # remove all objects and reinitialize table stats
    table.delete('all')
    in_game = False
    if paused_game: # remove paused game flags
        pause_game()
    red_Score = yellow_Score = 0

####################################################################################################
############################################# ACCOUNTS #############################################
####################################################################################################

def create_new_account(initials):
    """create a new user record, fill in user dictionary and save/apply new account

    Parameters
    ----------
    initials - string
        user input initials to be added to identify account"""

    # blank user dict
    new_Account = {
    "id":0,
    "initials":"",
    "level_Status" : [False]*8,
    "xp" : 0
    }

    #set user values
    new_Account["id"] = len(all_accounts)
    new_Account["initials"] = initials.upper().strip().replace("\n","")
    all_accounts[str(new_Account["id"])] = new_Account
    current_account_id.set(int(new_Account["id"])) # change current account to new account
    save_account_data() # save to file
    change_account() # change UI to match new user

def create_new_account_form():
    """Load menu options and controls to create a new user"""
    global announcement_text_overlay

    # clear active UI elements not related to current page
    announcement_text_overlay = ""
    end_current_game()
    hide_menu_elements()
    top_Status_bar.set("Create new account")
    secondary_description.set("upon creation you will be signed in")
    
    # create form for user input
    templabel = Label(table,text="Enter Your Initials",font=("Helvetica",15,'bold'))
    templabel.place(x=TABLE_LENGTH/2,y=50,anchor="center")
    temp_widgets.append(templabel) # add to temp reference array to be destroyed on changing screen
    # initials input box
    new_user_input_initials_box.place(x=TABLE_LENGTH/2,y=150,anchor="center")
    # create button
    temp_b1 = Button(table,text= "Create User",font=("Helvetica",15,'bold'), bg=PRIMARY_BUTTON_COLOR, command=create_account_clicked)
    temp_b1.place(x=TABLE_LENGTH/2,y=250,anchor="center")
    temp_widgets.append(temp_b1)# add to temp reference array to be destroyed on changing screen

def Load_account_form():
    """ Show all existing accounts for user to select """
    global announcement_text_overlay
    
    # clear active UI elements not related to current page
    announcement_text_overlay = ""
    end_current_game()
    hide_menu_elements()

    top_Status_bar.set("Existing Accounts")
    secondary_description.set("Select your account to load progress")

    #Layout form
    prompt_lbl = Label(table,text="Choose Your Account",font=("Helvetica",15,'bold'))
    prompt_lbl.place(x=10,y=10)
    temp_widgets.append(prompt_lbl)
    ypos = 100
    xpos = 100
    # loop through users and place on table equally spaced
    # once at bottom of table, increase y and reset y to start new column
    for id,user in all_accounts.items(): # get each user and the id
        user_name = user["initials"]+"#"+str(user["id"]) # gamer tag
        new_button = Radiobutton(table,text= user_name ,variable=current_account_id, value= int(id) ,font=("Helvetica",15,'bold'), bg=PRIMARY_BUTTON_COLOR,command=change_account,indicatoron = 0)
        new_button.place(x=xpos,y=ypos,anchor="center")
        ypos+=50
        if ypos > TABLE_WIDTH: # at bottom of table, move onto the next column
            xpos+=200
            ypos = 100
        temp_widgets.append(new_button)# add to temp reference array to be destroyed on changing screen

def change_account():
    """ Change UI to match the current user selected"""
    current_user_selected_username.set(all_accounts[str(current_account_id.get())]["initials"]+"#"+str(all_accounts[str(current_account_id.get())]["id"]))

def create_account_clicked():
    """Create new account submitted by user"""
    # get users initials input and call for new account 
    create_new_account(initials=new_user_input_initials_box.get("1.0",'end'))
    select_Level() # back to menu

def save_account_data():
    """Save all account data to JSON files"""
    # save all account data
    f = open("./accounts.json","w")
    dump([all_accounts],f,indent=3) # use json dump to turn 2d dictionary to json format
    f.close()

def load_accounts():
    """Load all account data from JSON file"""
    global all_accounts
    # get account data
    f = open("./accounts.json","r")
    all_accounts = load(f)[0]# load from JSON format and save as 2d dictionary
    f.close()

####################################################################################################
########################################### INITIAL LAYOUT #########################################
####################################################################################################

def layout_elements():
    """Create and position static layout components of window"""
    #table and side bar background
    global table
    global paused_game_button
    global retry_button
    global back_to_menu_button
    global new_user_input_initials_box
    global instructions_button

    # main table initial state
    table = Canvas(window, background=TABLE_COLOR, width=TABLE_LENGTH, height=TABLE_WIDTH,cursor="cross",highlightbackground="black")
    table.place(x=TABLE_X_OFFSET,y=TABLE_Y_OFFSET)
    #Canvas(window, background=RHS_Background,width=SIDE_BAR_WIDTH,height=WINDOW_HEIGHT).place(x=0,y=0)
    # side bar layout
    Label(window, text=GAME_TITLE,font=("Helvetica",40,'bold'), bg=RHS_BACKGROUND, fg=TEXT_COLOR).place(x=20,y=20)
    Label(window, text=welcome_Label_text,font=("Helvetica",15), bg=RHS_BACKGROUND, fg=TEXT_COLOR).place(x=20,y=100)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="SELECT LEVEL",width=20,command=select_Level,font=("Helvetica",15,'bold')).place(x=25,y=200)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="NEW CO-OP",width=20,command=co_op_mode,font=("Helvetica",15,'bold')).place(x=25,y=250)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="LEADER BOARD",width=20,font=("Helvetica",15,'bold'), command=view_leader_board).place(x=25,y=300)
    pause_button_text.set("PAUSE") # initial state is running
    paused_game_button = Button(window,background=PRIMARY_BUTTON_COLOR,textvariable=pause_button_text,width=20,font=("Helvetica",15,'bold'), command=pause_game)
    instructions_button = Button(window,background=PRIMARY_BUTTON_COLOR,text="SHOW INSTRUCTIONS",width=20,font=("Helvetica",15,'bold'),command=show_instructions)
    instructions_button.place(x=25,y=550)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="SETTINGS",width=20,font=("Helvetica",15,'bold'),command=load_settings_menu).place(x=25,y=600)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="LOAD ACCOUNT",width=20,command=Load_account_form,font=("Helvetica",15,'bold')).place(x=25,y=700)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="CREATE ACCOUNT",width=20,command=create_new_account_form,font=("Helvetica",15,'bold')).place(x=25,y=750)
    Button(window,background=PRIMARY_BUTTON_COLOR,text="EXIT",width=20,command=exit_game,font=("Helvetica",15,'bold')).place(x=25,y=850)
    Label(window, text="USER:",font=("Helvetica",15), bg=RHS_BACKGROUND, fg=TEXT_COLOR).place(x=20,y=150)
    Label(window, textvariable=current_user_selected_username,font=("Helvetica",15), bg=RHS_BACKGROUND, fg=TEXT_COLOR).place(x=100,y=150)

    # select level menu options
    #row 1
    select_Level_buttons[0] = Radiobutton(table,image=LEVEL_1_BUTTON,variable=current_level_selected, value=1,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[1] = Radiobutton(table,image=LEVEL_2_BUTTON,variable=current_level_selected, value=2,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[2] = Radiobutton(table,image=LEVEL_3_BUTTON,variable=current_level_selected, value=3,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[3] = Radiobutton(table,image=LEVEL_4_BUTTON,variable=current_level_selected, value=4,command=Load_Selected_Level,indicatoron = 0)

    # row 2
    select_Level_buttons[4] = Radiobutton(table,image=LEVEL_5_BUTTON,variable=current_level_selected, value=5,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[5] = Radiobutton(table,image=LEVEL_6_BUTTON,variable=current_level_selected, value=6,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[6] = Radiobutton(table,image=LEVEL_7_BUTTON,variable=current_level_selected, value=7,command=Load_Selected_Level,indicatoron = 0)
    select_Level_buttons[7] = Radiobutton(table,image=LEVEL_8_BUTTON,variable=current_level_selected, value=8,command=Load_Selected_Level,indicatoron = 0)

    #Score and status bar
    Label(window, textvariable=top_Status_bar,font=("Helvetica",20,'bold'), bg=MID_BACKGROUND, fg=TEXT_COLOR).place(x=TABLE_X_OFFSET,y=20)
    Label(window, textvariable=secondary_description,font=("Helvetica",15,'bold'), bg=MID_BACKGROUND, fg=TEXT_COLOR).place(x=TABLE_X_OFFSET,y=60)
    Label(window, textvariable=current_game_score_text,font=("Helvetica",15,'bold'), bg=LHS_BACKGROUND, fg=TEXT_COLOR).place(x=WINDOW_WIDTH-100,y=60,anchor="e")
    Label(window, textvariable=current_game_shot_limit_left_text,font=("Helvetica",15,'bold'), bg=LHS_BACKGROUND, fg=TEXT_COLOR).place(x=WINDOW_WIDTH-100,y=90,anchor="e")
    Label(window, textvariable=current_game_time_limit_left_text,font=("Helvetica",15,'bold'), bg=LHS_BACKGROUND, fg=TEXT_COLOR).place(x=WINDOW_WIDTH-100,y=120,anchor="e")
    Label(window, textvariable=turn_announcer,font=("Helvetica",15,'bold'), bg=MID_BACKGROUND, fg=TEXT_COLOR).place(x=TABLE_X_OFFSET,y=100)
    Label(window, text="all menu buttons except PAUSE and INSTRUCTIONS will end a running game",font=("Helvetica",15,'bold'), bg=MID_BACKGROUND, fg=TEXT_COLOR).place(x=WINDOW_WIDTH/2,y=WINDOW_HEIGHT-20,anchor="center")

    # overlay menu options
    retry_button = Button(window, text="Restart Game",font=("Helvetica",20,'bold'),background=PRIMARY_BUTTON_COLOR,command=restartgame)
    back_to_menu_button = Button(window, text="Select a Level",font=("Helvetica",20,'bold'),background=PRIMARY_BUTTON_COLOR,command=select_Level)

    # create new account input box
    new_user_input_initials_box = Text(table, width= 25,height=1,font=("Helvetica",25,'bold'))

####################################################################################################
################################################ LEVELS ############################################
####################################################################################################

def Load_Selected_Level():
    """ Load user selected level and display game"""
    global ball_config_file_name
    global current_game_is_co_op
    global current_level_playing

    # clear active UI elements not related to current page
    hide_menu_elements()
    # find game config file and load game based on the config
    ball_config_file_name = "L"+str(current_level_selected.get())
    current_level_playing = current_level_selected.get()
    current_game_is_co_op = False # set mode to playing levels
    new_game_set_up()

####################################################################################################
############################################ LEADER BOARD ##########################################
####################################################################################################

def view_leader_board():
    """ load leader board 
    - Order by EXP descending, and display top 10 players
    - display current players xp"""

    # add to temp reference array to be destroyed on changing screen
    end_current_game()
    hide_menu_elements()

    top_Status_bar.set("Leaderboard")
    secondary_description.set("TOP 10 levels players")

    # order by xp
    sort_accounts = dict(sorted(all_accounts.items(), key=lambda item: item[1]["xp"],reverse=True))

    x =0
    # loop through list to layout to 10 leader board positions in 2 columns
    for acc in (sort_accounts):
        if x>9: # display only top 10
            break
        row_string = str(x+1)+" - "+all_accounts[acc]["initials"]+"#"+str(all_accounts[acc]["id"]) + " :: "+ str(all_accounts[acc]["xp"])+" xp"
        # position based on current x
        px = (100+(400*int(x>4)))
        py = (150+((x%5)*70))
        table.create_text(px,py,text=row_string,font=("Helvetica",20,'bold'),anchor="w")
        x+=1

    # display user sign in status
    if current_account_id.get() == -1:
        table.create_text((800),(100),text="YOU ARE NOT SIGNED IN",font=("Helvetica",20,'bold'))
    else:
        # show user account and current XP
        row_string = "You Are "+all_accounts[str(current_account_id.get())]["initials"]+"#"+str(all_accounts[str(current_account_id.get())]["id"]) + " :: "+ str(all_accounts[str(current_account_id.get())]["xp"])+" xp"
        table.create_text((800),(100),text=row_string,font=("Helvetica",20,'bold'))

####################################################################################################
############################################ Game Behavior #########################################
####################################################################################################

def game_Behavior():
    """ In game checks for rules and restrictions """
    check_for_winner() # check win status
    check_limits() # check if any level game limits have been spent
    check_who_next() # in co-op check who's turn based on game rules

def check_for_winner():
    """check for winner based on rules and set winning status"""
    global announcement_text_overlay
    global in_game

    # set red and yellow won flags
    red_won =  red_Score >= current_game_red_ball_target and current_game_red_ball_target >0
    yellow_won =  yellow_Score >= current_game_yellow_ball_target and current_game_yellow_ball_target >0
    # if 2 player game
    if current_game_is_co_op:
        # display winner and end game
        if red_won and yellow_won:
            announcement_text_overlay ="Draw"
            in_game = False
        elif red_won:
            announcement_text_overlay = "Red Won"
            in_game = False
        elif yellow_won:
            announcement_text_overlay = "Yellow Won"
            in_game = False
    else: # in level game
        # if any goal met, the user wins as one player game
        if red_won or yellow_won:
            # display leader board
            # if user signed in, the apply xp points
            if current_account_id.get() != -1:
                all_accounts[str(current_account_id.get())]["xp"] += current_game_xp_worth
                all_accounts[str(current_account_id.get())]["level_Status"][current_level_playing-1] = True
                view_leader_board()
                save_account_data()
                announcement_text_overlay ="Level Complete! +"+str(current_game_xp_worth)+" xp"
            else:
                view_leader_board()
                announcement_text_overlay ="Level Complete! +0 xp (no sign in)"
            in_game = False
        elif in_game:
            # check if white potted (instant fail level)
            if balls[0].potted:
                announcement_text_overlay ="FAILED - Potted The White Ball"
                view_leader_board()
                in_game = False

def check_limits():
    """ Check level game rules and conditions """
    global announcement_text_overlay
    global in_game
    global current_game_shot_limit_left
    global current_game_time_limit_left

    # count down for timed level games
    if not current_game_is_co_op and current_game_time_limit_left>0:
        # update number of seconds left
        current_game_time_limit_left = (current_game_end_time-datetime.today()).seconds

    # check if all shots spent
    if current_game_shot_limit_left == 0 and (not ball_in_motion) and in_game:
            announcement_text_overlay ="FAILED - Out of shots"
            view_leader_board()
            in_game = False
    # check if out of time
    if current_game_time_limit_left == 0 and (not ball_in_motion) and in_game:
            announcement_text_overlay ="FAILED - Out of time"
            view_leader_board()
            in_game = False
    
def game_Behavior_Ball_Potted(ball_color_potted):
    """ Ball potted event
    
    Parameters
    ----------
    ball_color_potted = string
        color of ball potted """
    global yellow_Score
    global red_Score
    global current_game_color_turn_to_go
    global in_game
    global announcement_text_overlay
    global current_game_foul_penalty
    global current_game_player_1_turn
    global current_game_red_potted_in_last_round
    global current_game_yellow_potted_in_last_round

    #if first ball potted, declare the colour assignment
    if current_game_color_turn_to_go =="":
        if ball_color_potted == YELLOW_COLOR:
            current_game_color_turn_to_go = "YELLOW"
        elif ball_color_potted == RED_COLOR:
            current_game_color_turn_to_go = "RED"

    # yellow or read ball - add to score
    if ball_color_potted == YELLOW_COLOR:
        yellow_Score +=1
        current_game_yellow_potted_in_last_round = True
    elif ball_color_potted == RED_COLOR:
        red_Score +=1
        current_game_red_potted_in_last_round = True

    # que ball potted
    elif ball_color_potted == QUE_BALL_COLOR:
        # turn terminated and 2 sho penalty applied
        current_game_player_1_turn = not current_game_player_1_turn
        if current_game_color_turn_to_go =="RED":
            current_game_color_turn_to_go ="YELLOW"
        elif current_game_color_turn_to_go =="YELLOW":
            current_game_color_turn_to_go ="RED"
        current_game_foul_penalty = 2
    
    # black ball potted events - declare winner
    elif ball_color_potted == BLACK_BALL_COLOR:
        in_game = False
        # display declared winner
        if current_game_color_turn_to_go == "": # no colors were assigned 
            announcement_text_overlay = "Black ball potted - Player "+ str(2-int(not current_game_player_1_turn)) + " WINS"
        elif current_game_color_turn_to_go == "RED":
            if(red_Score <7): # check if ball was potted last by the correct player for a win
                announcement_text_overlay = "Black ball potted - Player "+ str(2-int(not current_game_player_1_turn)) + " WINS"
            else:
                red_Score +=1 # ball potted last by player so win
        elif current_game_color_turn_to_go == "YELLOW":
            if(yellow_Score  <7): # check if ball was potted last by the correct player for a win
                announcement_text_overlay = "Black ball potted - Player "+ str(2-int(not current_game_player_1_turn)) + " WINS"
            else:
                yellow_Score +=1 # ball potted last by player so win

def check_who_next():
    """ check new players turn based on game rules and update for UI changes"""
    global current_game_player_1_turn
    global current_game_color_turn_to_go
    global current_game_foul_penalty
    global current_game_waiting_for_shot
    global current_game_red_potted_in_last_round
    global current_game_yellow_potted_in_last_round

    # if game running and in 2 player, and ball has stopped moving due to turn
    if current_game_is_co_op and (not ball_in_motion) and (not current_game_waiting_for_shot):
        current_game_waiting_for_shot = True

        # reset que ball if in pot
        if balls[0].potted:
            balls[0].reset_que_ball()

        if current_game_foul_penalty <1: # if not stay on same turn due to foal
            # check if user only potted their balls as this would result in another go
            if current_game_color_turn_to_go =="RED":
                if current_game_yellow_potted_in_last_round or (not current_game_red_potted_in_last_round):
                    # change turn
                    current_game_player_1_turn = not current_game_player_1_turn
                    current_game_color_turn_to_go ="YELLOW"
            elif current_game_color_turn_to_go =="YELLOW":
                if current_game_red_potted_in_last_round or (not current_game_yellow_potted_in_last_round):
                    # change turn
                    current_game_player_1_turn = not current_game_player_1_turn
                    current_game_color_turn_to_go ="RED"
            else: # no ball potted yet
                #change player
                current_game_player_1_turn = not current_game_player_1_turn
        
        # set player turn announcer on UI
        if current_game_color_turn_to_go == "":
            turn_announcer.set("Player "+ str(2-int(current_game_player_1_turn))+" your turn")
            if current_game_foul_penalty>0:
                turn_announcer.set("Player "+ str(2-int(current_game_player_1_turn))+" your turn and "+str(current_game_foul_penalty)+" goes due to Player "+str(2-int( not current_game_player_1_turn))+" foul")
        else:
            turn_announcer.set("Player "+ str(2-int(current_game_player_1_turn))+" your turn - you are colour "+current_game_color_turn_to_go)
            if current_game_foul_penalty>0:
                turn_announcer.set("Player "+ str(2-int(current_game_player_1_turn))+" your turn - you are colour "+str(current_game_color_turn_to_go)+" and "+str(current_game_foul_penalty)+" goes due to Player "+str(2-int( not current_game_player_1_turn))+" foul")
        
        # set flags as ready for next shot
        current_game_red_potted_in_last_round = False
        current_game_yellow_potted_in_last_round = False
        current_game_foul_penalty -= 1


####################################################################################################
############################################### CONTROLS ###########################################
####################################################################################################
def exit_game():
    """ User exit game - close window """
    window.destroy()

def pause_game():
    """toggle game pause state"""
    global paused_game
    global announcement_text_overlay
    global overlay_menu_show
    ## check if game paused and toggle state and UI
    if paused_game:
        pause_button_text.set("PAUSE")
        announcement_text_overlay = ""
        overlay_menu_show = False
        paused_game = False
    else:
        if in_game:
            pause_button_text.set("RESUME")
            announcement_text_overlay = "PAUSED"
            overlay_menu_show = True
            paused_game = True

def pause_key(self):
    """Event driven Pause key call pause game toggle """
    pause_game()

def boss_key(self):
    """ Boss key cheat toggle """
    global show_boss_key_image
    # pause game
    if not paused_game:
        pause_game()
    
    # toggle boss key image display
    show_boss_key_image = not show_boss_key_image

def mouse_move_change_targeting_line(event):
    """ change targeting line for que ball on mouse move """
    global aim_line_Of_Impact_Angle

    # if in game and ready to shoot
    if (not paused_game) and (in_game) and (not ball_in_motion):
        # get coordinates of mouse and que ball
        x, y = event.x, event.y
        x0, y0 = balls[0].position_x, balls[0].position_y
        table.coords(aim_guide_line,x0,y0,x,y) # draw aiming line
        # solve the aiming line direction
        aim_line_Of_Impact_Angle = direction_between_2_points(from_x=x0,from_y=y0,to_x=x,to_y=y)

def strike(event):
    """ when user strikes ball, input new force into que ball """
    global current_game_shot_limit_left
    global ball_in_motion
    global current_game_waiting_for_shot

    # ball velocities
    #400 casual slow
    #500 casual fast
    #650 rapid
    #800 break

    #if game in progress and ball stationary waiting for shot
    if (not paused_game) and (in_game) and (not ball_in_motion):
        # set ball in motion flags
        ball_in_motion = True
        current_game_waiting_for_shot = False
        # apply new force to que ball
        balls[0].set_velocity_direction(velocity=650,direction=aim_line_Of_Impact_Angle)
        table.coords(aim_guide_line,0,0,0,0) # hide targeting line
        # in level game, spend a shot
        if not current_game_is_co_op:
                current_game_shot_limit_left -=1

####################################################################################################
############################################# CHEAT CODES ##########################################
####################################################################################################
def increase_pocket_size(self):
    """ CHEAT - change pocket size between 40px to 90px"""
    global increase_pocket_size_on

    if in_game:
        # toggle between default pocket size and increased
        if increase_pocket_size_on:
                add_pockets_to_table()
        else:
            add_pockets_to_table(size=90)
        increase_pocket_size_on = not increase_pocket_size_on

def instant_win(self):
    """CHEAT - instant win
    - levels = always win
    - co op = (colour ball:player) need to be already assigned """
    global yellow_Score
    global red_Score
    # if in game, set scores based on game modes
    if in_game:
        if current_game_is_co_op:
            # set current player taking turn as winner
            if current_game_color_turn_to_go =="RED":
                red_Score = 8
            elif current_game_color_turn_to_go =="YELLOW":
                yellow_Score = 8

        else: # level game
            yellow_Score = current_game_yellow_ball_target
            red_Score = current_game_red_ball_target
####################################################################################################
############################################### Game Loop ##########################################
####################################################################################################

def stats_updater():
    """Update UI stats (show/hide) and values based on game state"""
   
    if announcement_text_overlay == "":
        # remove from screen
        announcement_Label.place_forget()
        retry_button.place_forget()
        back_to_menu_button.place_forget()
    else:
        # place in centre and load menu buttons
        announcement_Label.lift() # move to top
        announcement_Label.place(x= TABLE_X_OFFSET+ TABLE_LENGTH/2,y = TABLE_Y_OFFSET,anchor = 'center')
        announcement_Label.config(text=announcement_text_overlay)
        retry_button.place(x= TABLE_X_OFFSET+ TABLE_LENGTH-200,y =  TABLE_Y_OFFSET+ TABLE_WIDTH-300,anchor = 'center')
        back_to_menu_button.place(x= TABLE_X_OFFSET+ TABLE_LENGTH-200,y =  TABLE_Y_OFFSET+ TABLE_WIDTH-200,anchor = 'center')
        # change menu for select level button based on current game type playing
        if current_game_is_co_op:
            back_to_menu_button.config(text="End Game")
        else:
            back_to_menu_button.config(text="Select a Level")

    if in_game:
        paused_game_button.place(x=25,y=400)
        # set ui display for game limits
        current_game_shot_limit_left_text.set("")
        current_game_time_limit_left_text.set("")
        if not current_game_is_co_op:
            if current_game_shot_limit_left >= 0:
                current_game_shot_limit_left_text.set(str(current_game_shot_limit_left)+" shots left")

            if current_game_time_limit_left >= 0:
                current_game_time_limit_left_text.set(str(current_game_time_limit_left)+" secs left")

        # DISPLAY CURRENT SCORE
        current_game_score_text.set(str(yellow_Score)+" Y : "+str(red_Score)+" R")

    else:
        # hide game stats elements
        paused_game_button.place_forget()
        current_game_shot_limit_left_text.set("")
        current_game_time_limit_left_text.set("")
        current_game_score_text.set("")

    if show_boss_key_image:
        # display boss key image
        boss_key_overlay.lift()  # move to top
        boss_key_overlay.place(x=-2,y=-2)
    else: # hide
        boss_key_overlay.place_forget()

    if instructions_showing:
        # display instructions
        instructions_display.place(x=TABLE_X_OFFSET,y=TABLE_Y_OFFSET-150)
        instructions_button.config(text="HIDE INSTRUCTIONS")
        instructions_display.lift()
    else: # hide
        instructions_display.place_forget()
        instructions_button.config(text="SHOW INSTRUCTIONS")

def running_game_logic():
    """ check for game collisions, then move balls on table if not potted"""
    pot_collision() # check if potted
    ball_collision() # check for collisions and work out new velocities

    # move all balls based on velocities
    for ball in balls:
        ball.move_Logic()

def game_loop():
    """game in session loop
    - check game rules
    - update UI
    - run game movement checks and implementation
    - set ball moving flag"""
    global ball_in_motion

    # check game rules and update stats
    game_Behavior()
    stats_updater()

    # run checks, perform logic and update UI
    if not paused_game and in_game:
        ball_in_motion =  any(ball.check_if_momentum() for ball in balls)
        running_game_logic()

    window.after(10,game_loop) # set timing for smoothness of motion, and speed of ball


####################################################################################################
################################################# Menus ############################################
####################################################################################################

def select_Level():
    """ Display menu options to load a level """
    global current_game_is_co_op
    global announcement_text_overlay

    # clear active UI elements not related to current page
    hide_menu_elements()
    end_current_game()
    announcement_text_overlay = ""

    # set page description
    top_Status_bar.set("Select A Level")
    secondary_description.set("Level 1-8")
    current_game_score_text.set("")
    turn_announcer.set("")
    # set to levels mode
    current_game_is_co_op = False
    # display menu options and tick if level completed by user
    starting_x = 20
    starting_y = 20
    for x in range(len(select_Level_buttons)):
        if x==4: # new row
            starting_y = 275
            starting_x = 20
        select_Level_buttons[x].place(x=starting_x,y = starting_y)
        #check if ticked
        if current_account_id.get() !=-1:
            user_completed = all_accounts[str(current_account_id.get())]["level_Status"][x]
            if user_completed:
                # add tick over level image
                new_tick = Label(table,image=COMPLETED_LEVEL_IMAGE,borderwidth=0)
                new_tick.place(x =(starting_x+170),y = (starting_y + 170))
                temp_widgets.append(new_tick)

        starting_x+= 260

def co_op_mode():
    """ Load a new co op game """
    global ball_config_file_name
    global current_game_is_co_op
    global announcement_text_overlay
    # set up new game, and load standard game config
    current_game_is_co_op = True
    ball_config_file_name = "Standard"
    announcement_text_overlay = ""
    new_game_set_up()

def hide_menu_elements():
    """hide all menu elements - clear temporary widgets for new view """
    global temp_widgets
    global instructions_showing

    # clear all temp widgets
    for x in temp_widgets:
        x.place_forget()
    
    temp_widgets = []

    # clear canvas
    table.delete('all')

    # hide user initials text box
    new_user_input_initials_box.place_forget()

    # hide select level buttons
    for b in select_Level_buttons:
        b.place_forget()
    
    instructions_display.place_forget()
    instructions_showing = False

def show_instructions():
    """ Toggle instructions show without ending game"""
    global instructions_showing
    instructions_showing = not instructions_showing

def restartgame():
    """reset game - reload from game config file"""
    global announcement_text_overlay
    announcement_text_overlay = ""
    new_game_set_up()

####################################################################################################
############################################# Settings #############################################
####################################################################################################
def load_settings():
    """ load current settings from file """
    global user_settings
    #get current config from file
    f = open("./settings.json","r")
    user_settings = load(f)[0] # load json to dict
    f.close()
    #bindings
    window.bind('<'+user_settings["strike"]+'>', strike)
    window.bind('<'+user_settings["pause"]+'>', pause_key)
    window.bind('<'+user_settings["boss"]+'>', boss_key)
    # cheat code key bindings
    window.bind('<'+user_settings["pockets"]+'>', increase_pocket_size)
    window.bind('<'+user_settings["win"]+'>', instant_win)

def save_settings_data():
    """ save current settings to file"""
    f = open("./settings.json","w")
    dump([user_settings],f,indent=3) # save dict to json
    f.close()

def load_settings_menu():
    """ display setting menu form"""
    global announcement_text_overlay

    # clear active UI elements not related to current page
    announcement_text_overlay = ""
    end_current_game()
    hide_menu_elements()
    top_Status_bar.set("Settings")
    secondary_description.set("Change key bindings")

    # lay out form and save in temp_widgets to be destroyed later
    temp_l0 = Label(table,text="CTRL = Control-Key\na-z = a-z\n0-9 = 0-9\ne.g. CTRL+A = Control-Key-a\n\n\nPAUSE - button to pause the game\nStrike - button to hit the que ball\nBoss - button to hide game\nPockets - cheat(increase pocket size using button\nWin - cheat(instant win button))",font=("Helvetica",15,'bold'),bg=TABLE_COLOR)
    temp_l0.place(x=400,y=70)
    temp_widgets.append(temp_l0)

    temp_l1 = Label(table,text="Settings - change key bindings",font=("Helvetica",15,'bold'),bg=TABLE_COLOR)
    temp_l1.place(x=50,y=50)
    temp_widgets.append(temp_l1)

    temp_l2 = Label(table,text="Pause button",font=("Helvetica",12,'bold'),bg=TABLE_COLOR)
    temp_l2.place(x=50,y=100)
    temp_widgets.append(temp_l2)

    temp_t2 = Text(table,font=("Helvetica",14,'bold'),height=1,width=20)
    temp_t2.insert('end',user_settings["pause"])
    temp_t2.place(x=50,y=125)
    setting_options.append(temp_t2)

    temp_l3 = Label(table,text="Strike button",font=("Helvetica",12,'bold'),bg=TABLE_COLOR)
    temp_l3.place(x=50,y=170)
    temp_widgets.append(temp_l3)

    temp_t3 = Text(table,font=("Helvetica",14,'bold'),height=1,width=20)
    temp_t3.insert('end',user_settings["strike"])
    temp_t3.place(x=50,y=200)
    setting_options.append(temp_t3)


    temp_l4 = Label(table,text="Boss button",font=("Helvetica",12,'bold'),bg=TABLE_COLOR)
    temp_l4.place(x=50,y=250)
    temp_widgets.append(temp_l4)

    temp_t4 = Text(table,font=("Helvetica",14,'bold'),height=1,width=20)
    temp_t4.insert('end',user_settings["boss"])
    temp_t4.place(x=50,y=280)
    setting_options.append(temp_t4)

    temp_l5 = Label(table,text="Pockets button",font=("Helvetica",12,'bold'),bg=TABLE_COLOR)
    temp_l5.place(x=50,y=330)
    temp_widgets.append(temp_l5)

    temp_t5 = Text(table,font=("Helvetica",14,'bold'),height=1,width=20)
    temp_t5.insert('end',user_settings["pockets"])
    temp_t5.place(x=50,y=360)
    setting_options.append(temp_t5)

    temp_l6 = Label(table,text="Win button",font=("Helvetica",12,'bold'),bg=TABLE_COLOR)
    temp_l6.place(x=50,y=410)
    temp_widgets.append(temp_l6)

    temp_t6 = Text(table,font=("Helvetica",14,'bold'),height=1,width=20)
    temp_t6.insert('end',user_settings["win"])
    temp_t6.place(x=50,y=440)
    setting_options.append(temp_t6)

    #move into disposable widget collection to be destroyed on screen change
    for x in setting_options:
        temp_widgets.append(x)

    temp_b1 = Button(table, text="Save Changes",font=("Helvetica",15,'bold'), bg=PRIMARY_BUTTON_COLOR, command=set_settings)
    temp_b1.place(x=50,y=480)
    temp_widgets.append(temp_b1)

def set_settings():
    """save settings from form"""
    global user_settings
    global setting_options
    # get settings form value
    user_settings["pause"] = setting_options[0].get("1.0",'end').strip()
    user_settings["strike"] = setting_options[1].get("1.0",'end').strip()
    user_settings["boss"] = setting_options[2].get("1.0",'end').strip()
    user_settings["pockets"] = setting_options[3].get("1.0",'end').strip()
    user_settings["win"] = setting_options[4].get("1.0",'end').strip()
    setting_options=[]
    # reload key bindings and save new settings to file
    save_settings_data()
    load_settings()
    select_Level()

####################################################################################################
#################################### Constants and initial state ###################################
####################################################################################################

def configure_window():
    """Set up window properties before starting game loop"""
    window.title(GAME_TITLE)
    window.geometry(str(WINDOW_WIDTH)+"x"+str(WINDOW_HEIGHT))
    window.configure(background=BG_COLOR)
    window.attributes("-fullscreen", True)
    layout_elements()

load_settings() # load initial settings
load_accounts() # load existing accounts
configure_window() # set up window
select_Level() # initial menu - open select level menu
game_loop() # start game loop

window.mainloop()

####################################################################################################
############################################# RESOURCES ############################################
####################################################################################################
### background_gradient.png made using coolors.co
### get_difference_in_angles formula resource from https://stackoverflow.com/a/2007279/13332484 by peter b