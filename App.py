"""
Linhas Aéreas ED-II - Airline Management System
A Flask web application for managing airline operations including:
- Passenger Module: Flight search, booking, reservations, miles
- Admin Module: Authentication, flight/client management
"""

from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify
import json
import os
import hashlib
import uuid
from datetime import datetime
from functools import wraps

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'linhas-aereas-ed-ii-secret-key')

# Data directories
DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')

# ============================================================================
# DATA STRUCTURES
# ============================================================================

class BTreeNode:
    """B-Tree Node for client storage and optimized queries"""
    def __init__(self, leaf=True):
        self.leaf = leaf
        self.keys = []  # List of (key, client_data) tuples
        self.children = []
    
    def to_dict(self):
        return {
            'leaf': self.leaf,
            'keys': self.keys,
            'children': [c.to_dict() for c in self.children]
        }
    
    @staticmethod
    def from_dict(data):
        node = BTreeNode(data['leaf'])
        node.keys = data['keys']
        node.children = [BTreeNode.from_dict(c) for c in data['children']]
        return node


class BTree:
    """B-Tree implementation for client management with optimized queries"""
    def __init__(self, t=3):
        self.root = BTreeNode()
        self.t = t  # Minimum degree
    
    def search(self, key, node=None):
        """Search for a client by key (CPF or name)"""
        if node is None:
            node = self.root
        
        i = 0
        while i < len(node.keys) and key > node.keys[i][0]:
            i += 1
        
        if i < len(node.keys) and key == node.keys[i][0]:
            return node.keys[i][1]
        
        if node.leaf:
            return None
        
        return self.search(key, node.children[i])
    
    def insert(self, key, data):
        """Insert a new client into the B-Tree"""
        root = self.root
        
        if len(root.keys) == (2 * self.t) - 1:
            new_root = BTreeNode(leaf=False)
            new_root.children.append(self.root)
            self._split_child(new_root, 0)
            self.root = new_root
            self._insert_non_full(new_root, key, data)
        else:
            self._insert_non_full(root, key, data)
    
    def _split_child(self, parent, i):
        """Split a full child node"""
        t = self.t
        child = parent.children[i]
        new_node = BTreeNode(leaf=child.leaf)
        
        parent.keys.insert(i, child.keys[t - 1])
        parent.children.insert(i + 1, new_node)
        
        new_node.keys = child.keys[t:]
        child.keys = child.keys[:t - 1]
        
        if not child.leaf:
            new_node.children = child.children[t:]
            child.children = child.children[:t]
    
    def _insert_non_full(self, node, key, data):
        """Insert into a non-full node"""
        i = len(node.keys) - 1
        
        if node.leaf:
            # Update if key exists
            for j, (k, _) in enumerate(node.keys):
                if k == key:
                    node.keys[j] = (key, data)
                    return
            
            # Insert new key
            node.keys.append((key, data))
            node.keys.sort(key=lambda x: x[0])
        else:
            while i >= 0 and key < node.keys[i][0]:
                i -= 1
            i += 1
            
            if len(node.children[i].keys) == (2 * self.t) - 1:
                self._split_child(node, i)
                if key > node.keys[i][0]:
                    i += 1
            
            self._insert_non_full(node.children[i], key, data)
    
    def delete(self, key):
        """Delete a client from the B-Tree"""
        self._delete(self.root, key)
        if len(self.root.keys) == 0 and not self.root.leaf:
            self.root = self.root.children[0] if self.root.children else BTreeNode()
    
    def _delete(self, node, key):
        """Helper method for deletion"""
        i = 0
        while i < len(node.keys) and key > node.keys[i][0]:
            i += 1
        
        if node.leaf:
            if i < len(node.keys) and node.keys[i][0] == key:
                node.keys.pop(i)
            return
        
        if i < len(node.keys) and node.keys[i][0] == key:
            # Key found in internal node - replace with predecessor
            pred_node = node.children[i]
            while not pred_node.leaf:
                pred_node = pred_node.children[-1]
            node.keys[i] = pred_node.keys[-1]
            self._delete(node.children[i], pred_node.keys[-1][0])
        else:
            self._delete(node.children[i], key)
    
    def get_all_clients(self, node=None):
        """Get all clients in order"""
        if node is None:
            node = self.root
        
        clients = []
        for i, (key, data) in enumerate(node.keys):
            if not node.leaf and i < len(node.children):
                clients.extend(self.get_all_clients(node.children[i]))
            clients.append(data)
        
        if not node.leaf and len(node.children) > len(node.keys):
            clients.extend(self.get_all_clients(node.children[-1]))
        
        return clients
    
    def search_by_initial(self, initial):
        """Search clients by initial letter of name"""
        all_clients = self.get_all_clients()
        return [c for c in all_clients if c.get('nome', '').upper().startswith(initial.upper())]
    
    def search_by_name(self, name):
        """Search client by exact name"""
        all_clients = self.get_all_clients()
        for c in all_clients:
            if c.get('nome', '').lower() == name.lower():
                return c
        return None
    
    def to_dict(self):
        return {'t': self.t, 'root': self.root.to_dict()}
    
    @staticmethod
    def from_dict(data):
        btree = BTree(data['t'])
        btree.root = BTreeNode.from_dict(data['root'])
        return btree


class FlightGraph:
    """Graph implementation for flight route simulation and connections"""
    def __init__(self):
        self.vertices = {}  # airport_code -> airport_info
        self.edges = {}  # airport_code -> [(destination, flight_info), ...]
    
    def add_airport(self, code, name):
        """Add an airport vertex"""
        if code not in self.vertices:
            self.vertices[code] = {'code': code, 'name': name}
            self.edges[code] = []
    
    def add_flight(self, flight):
        """Add a flight as an edge between airports"""
        origin = flight['origem']
        destination = flight['destino']
        
        # Ensure airports exist
        self.add_airport(origin, origin)
        self.add_airport(destination, destination)
        
        # Add edge
        self.edges[origin].append((destination, flight))
    
    def remove_flight(self, flight_code):
        """Remove a flight edge"""
        for origin in self.edges:
            self.edges[origin] = [(d, f) for d, f in self.edges[origin] if f['codigo'] != flight_code]
    
    def find_direct_flights(self, origin, destination):
        """Find direct flights between two airports"""
        if origin not in self.edges:
            return []
        return [(d, f) for d, f in self.edges[origin] if d == destination]
    
    def find_connections(self, origin, destination, max_stops=2):
        """Find flight connections using BFS with limited stops"""
        if origin not in self.edges:
            return []
        
        paths = []
        queue = [(origin, [], 0)]  # (current, path, stops)
        
        while queue:
            current, path, stops = queue.pop(0)
            
            if current == destination and path:
                paths.append(path)
                continue
            
            if stops > max_stops:
                continue
            
            for dest, flight in self.edges.get(current, []):
                if dest not in [f['origem'] for f in path]:  # Avoid cycles
                    new_path = path + [flight]
                    if dest == destination:
                        paths.append(new_path)
                    elif stops < max_stops:
                        queue.append((dest, new_path, stops + 1))
        
        return paths
    
    def get_all_destinations_from(self, origin):
        """Get all reachable destinations from origin"""
        visited = set()
        destinations = []
        queue = [origin]
        
        while queue:
            current = queue.pop(0)
            if current in visited:
                continue
            visited.add(current)
            
            for dest, flight in self.edges.get(current, []):
                if dest not in visited:
                    destinations.append({'airport': dest, 'via': current})
                    queue.append(dest)
        
        return destinations
    
    def to_dict(self):
        return {'vertices': self.vertices, 'edges': self.edges}
    
    @staticmethod
    def from_dict(data):
        graph = FlightGraph()
        graph.vertices = data.get('vertices', {})
        graph.edges = data.get('edges', {})
        return graph


# ============================================================================
# DATA PERSISTENCE
# ============================================================================

def ensure_data_dir():
    """Ensure data directory exists"""
    if not os.path.exists(DATA_DIR):
        os.makedirs(DATA_DIR)

def load_json_file(filename, default=None):
    """Load data from JSON file"""
    ensure_data_dir()
    filepath = os.path.join(DATA_DIR, filename)
    if os.path.exists(filepath):
        with open(filepath, 'r', encoding='utf-8') as f:
            return json.load(f)
    return default if default is not None else {}

def save_json_file(filename, data):
    """Save data to JSON file"""
    ensure_data_dir()
    filepath = os.path.join(DATA_DIR, filename)
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


# ============================================================================
# DATA MANAGEMENT FUNCTIONS
# ============================================================================

def get_users():
    """Get users dictionary for authentication"""
    users = load_json_file('users.json', {})
    if not users:
        # Create default admin user
        users = {
            'admin': {
                'password': hashlib.sha256('admin123'.encode()).hexdigest(),
                'role': 'admin',
                'name': 'Administrador'
            }
        }
        save_json_file('users.json', users)
    return users

def save_users(users):
    """Save users dictionary"""
    save_json_file('users.json', users)

def get_flights():
    """Get all flights"""
    return load_json_file('flights.json', [])

def save_flights(flights):
    """Save flights"""
    save_json_file('flights.json', flights)

def get_flight_graph():
    """Get flight graph from stored flights"""
    graph = FlightGraph()
    flights = get_flights()
    for flight in flights:
        graph.add_flight(flight)
    return graph

def get_clients_btree():
    """Get clients B-Tree"""
    data = load_json_file('clients_btree.json')
    if data:
        return BTree.from_dict(data)
    return BTree()

def save_clients_btree(btree):
    """Save clients B-Tree"""
    save_json_file('clients_btree.json', btree.to_dict())

def get_reservations():
    """Get reservations dictionary"""
    return load_json_file('reservations.json', {})

def save_reservations(reservations):
    """Save reservations"""
    save_json_file('reservations.json', reservations)

def get_purchases():
    """Get purchases list"""
    return load_json_file('purchases.json', [])

def save_purchases(purchases):
    """Save purchases"""
    save_json_file('purchases.json', purchases)


# ============================================================================
# AUTHENTICATION DECORATOR
# ============================================================================

def login_required(f):
    """Decorator to require login for routes"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user' not in session:
            flash('Por favor, faça login para acessar esta página.', 'warning')
            return redirect(url_for('admin_login'))
        return f(*args, **kwargs)
    return decorated_function


def admin_required(f):
    """Decorator to require admin role"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'user' not in session:
            flash('Por favor, faça login para acessar esta página.', 'warning')
            return redirect(url_for('admin_login'))
        if session.get('role') != 'admin':
            flash('Acesso negado. Requer privilégios de administrador.', 'danger')
            return redirect(url_for('index'))
        return f(*args, **kwargs)
    return decorated_function


# ============================================================================
# PUBLIC ROUTES (PASSENGER MODULE)
# ============================================================================

@app.route('/')
def index():
    """Home page"""
    flights = get_flights()
    return render_template('index.html', flights=flights)


@app.route('/search_flights', methods=['GET', 'POST'])
def search_flights():
    """Search for available flights"""
    flights = get_flights()
    origins = list(set(f['origem'] for f in flights))
    destinations = list(set(f['destino'] for f in flights))
    
    if request.method == 'POST':
        origin = request.form.get('origin', '')
        destination = request.form.get('destination', '')
        
        graph = get_flight_graph()
        
        # Find direct flights
        direct = graph.find_direct_flights(origin, destination)
        direct_flights = [f for _, f in direct]
        
        # Find connections
        connections = graph.find_connections(origin, destination)
        
        return render_template('search_results.html',
                             origin=origin,
                             destination=destination,
                             direct_flights=direct_flights,
                             connections=connections)
    
    return render_template('search_flights.html', origins=origins, destinations=destinations)


@app.route('/simulate_route', methods=['GET', 'POST'])
def simulate_route():
    """Simulate flight routes using graph"""
    flights = get_flights()
    airports = list(set(f['origem'] for f in flights) | set(f['destino'] for f in flights))
    
    if request.method == 'POST':
        origin = request.form.get('origin', '')
        destination = request.form.get('destination', '')
        
        graph = get_flight_graph()
        
        # Find all possible routes
        routes = graph.find_connections(origin, destination, max_stops=3)
        
        # Calculate total miles and price for each route
        route_details = []
        for route in routes:
            total_miles = sum(f.get('milhas', 0) for f in route)
            total_price = sum(f.get('preco', 0) for f in route)
            route_details.append({
                'flights': route,
                'total_miles': total_miles,
                'total_price': total_price,
                'stops': len(route) - 1
            })
        
        # Sort by price
        route_details.sort(key=lambda x: x['total_price'])
        
        return render_template('route_simulation.html',
                             origin=origin,
                             destination=destination,
                             routes=route_details,
                             airports=airports)
    
    return render_template('route_simulation.html', airports=airports, routes=None)


@app.route('/book_flight/<flight_code>')
def book_flight(flight_code):
    """Book a single flight"""
    flights = get_flights()
    flight = next((f for f in flights if f['codigo'] == flight_code), None)
    
    if not flight:
        flash('Voo não encontrado.', 'danger')
        return redirect(url_for('search_flights'))
    
    if flight.get('assentos_disponiveis', 0) <= 0:
        flash('Não há assentos disponíveis neste voo.', 'warning')
        return redirect(url_for('search_flights'))
    
    return render_template('book_flight.html', flight=flight)


@app.route('/book_route', methods=['POST'])
def book_route():
    """Book a complete route (multiple flights)"""
    flight_codes = request.form.getlist('flight_codes')
    flights = get_flights()
    
    selected_flights = [f for f in flights if f['codigo'] in flight_codes]
    
    if not selected_flights:
        flash('Nenhum voo selecionado.', 'warning')
        return redirect(url_for('simulate_route'))
    
    # Check availability for all flights
    for flight in selected_flights:
        if flight.get('assentos_disponiveis', 0) <= 0:
            flash(f'Voo {flight["codigo"]} não tem assentos disponíveis.', 'warning')
            return redirect(url_for('simulate_route'))
    
    total_price = sum(f.get('preco', 0) for f in selected_flights)
    total_miles = sum(f.get('milhas', 0) for f in selected_flights)
    
    return render_template('book_route.html', 
                         flights=selected_flights,
                         total_price=total_price,
                         total_miles=total_miles)


@app.route('/confirm_booking', methods=['POST'])
def confirm_booking():
    """Confirm booking and generate reservation code"""
    cpf = request.form.get('cpf', '').strip()
    nome = request.form.get('nome', '').strip()
    flight_codes = request.form.getlist('flight_codes')
    data_viagem = request.form.get('data_viagem', datetime.now().strftime('%Y-%m-%d'))
    
    if not cpf or not nome:
        flash('CPF e nome são obrigatórios.', 'danger')
        return redirect(url_for('index'))
    
    flights = get_flights()
    selected_flights = [f for f in flights if f['codigo'] in flight_codes]
    
    if not selected_flights:
        flash('Nenhum voo selecionado.', 'warning')
        return redirect(url_for('search_flights'))
    
    # Generate reservation code
    reservation_code = str(uuid.uuid4())[:8].upper()
    
    # Calculate totals
    total_price = sum(f.get('preco', 0) for f in selected_flights)
    total_miles = sum(f.get('milhas', 0) for f in selected_flights)
    
    # Update seat availability
    for flight in flights:
        if flight['codigo'] in flight_codes:
            flight['assentos_disponiveis'] = max(0, flight.get('assentos_disponiveis', 0) - 1)
    save_flights(flights)
    
    # Create reservation
    reservations = get_reservations()
    reservations[reservation_code] = {
        'codigo_reserva': reservation_code,
        'cpf': cpf,
        'nome': nome,
        'voos': flight_codes,
        'data_viagem': data_viagem,
        'preco_total': total_price,
        'milhas_acumuladas': total_miles,
        'data_reserva': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
        'status': 'confirmada'
    }
    save_reservations(reservations)
    
    # Record purchase
    purchases = get_purchases()
    purchases.append({
        'codigo_reserva': reservation_code,
        'cpf': cpf,
        'nome': nome,
        'voos': flight_codes,
        'preco_total': total_price,
        'data_compra': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    })
    save_purchases(purchases)
    
    # Update client in B-Tree
    btree = get_clients_btree()
    existing_client = btree.search(cpf)
    
    if existing_client:
        # Update existing client
        existing_client['reservas'].append(reservation_code)
        existing_client['milhas_acumuladas'] = existing_client.get('milhas_acumuladas', 0) + total_miles
        btree.insert(cpf, existing_client)
    else:
        # Create new client
        client_data = {
            'cpf': cpf,
            'nome': nome,
            'reservas': [reservation_code],
            'data_cadastro': datetime.now().strftime('%Y-%m-%d'),
            'milhas_acumuladas': total_miles
        }
        btree.insert(cpf, client_data)
    
    save_clients_btree(btree)
    
    flash(f'Reserva confirmada! Código: {reservation_code}', 'success')
    return render_template('booking_confirmation.html',
                         reservation_code=reservation_code,
                         flights=selected_flights,
                         total_price=total_price,
                         total_miles=total_miles,
                         nome=nome,
                         cpf=cpf,
                         data_viagem=data_viagem)


@app.route('/check_reservation', methods=['GET', 'POST'])
def check_reservation():
    """Check reservation status"""
    if request.method == 'POST':
        code = request.form.get('reservation_code', '').strip().upper()
        
        reservations = get_reservations()
        reservation = reservations.get(code)
        
        if reservation:
            flights = get_flights()
            flight_details = [f for f in flights if f['codigo'] in reservation.get('voos', [])]
            return render_template('reservation_details.html', 
                                 reservation=reservation,
                                 flights=flight_details)
        else:
            flash('Reserva não encontrada.', 'warning')
    
    return render_template('check_reservation.html')


@app.route('/check_miles', methods=['GET', 'POST'])
def check_miles():
    """Check accumulated miles for a client"""
    if request.method == 'POST':
        cpf = request.form.get('cpf', '').strip()
        
        btree = get_clients_btree()
        client = btree.search(cpf)
        
        if client:
            return render_template('miles_info.html', client=client)
        else:
            flash('Cliente não encontrado.', 'warning')
    
    return render_template('check_miles.html')


# ============================================================================
# ADMIN ROUTES (ADMINISTRATIVE MODULE)
# ============================================================================

@app.route('/admin/login', methods=['GET', 'POST'])
def admin_login():
    """Admin login page"""
    if request.method == 'POST':
        username = request.form.get('username', '')
        password = request.form.get('password', '')
        
        users = get_users()
        user = users.get(username)
        
        if user and user['password'] == hashlib.sha256(password.encode()).hexdigest():
            session['user'] = username
            session['role'] = user.get('role', 'staff')
            session['name'] = user.get('name', username)
            flash(f'Bem-vindo, {user.get("name", username)}!', 'success')
            return redirect(url_for('admin_dashboard'))
        else:
            flash('Usuário ou senha inválidos.', 'danger')
    
    return render_template('admin/login.html')


@app.route('/admin/logout')
def admin_logout():
    """Admin logout"""
    session.clear()
    flash('Logout realizado com sucesso.', 'info')
    return redirect(url_for('index'))


@app.route('/admin')
@login_required
def admin_dashboard():
    """Admin dashboard"""
    flights = get_flights()
    reservations = get_reservations()
    btree = get_clients_btree()
    clients = btree.get_all_clients()
    
    stats = {
        'total_flights': len(flights),
        'total_reservations': len(reservations),
        'total_clients': len(clients),
        'total_seats': sum(f.get('assentos', 0) for f in flights),
        'available_seats': sum(f.get('assentos_disponiveis', 0) for f in flights)
    }
    
    return render_template('admin/dashboard.html', stats=stats)


# Flight Management
@app.route('/admin/flights')
@login_required
def admin_flights():
    """List all flights"""
    flights = get_flights()
    return render_template('admin/flights.html', flights=flights)


@app.route('/admin/flights/add', methods=['GET', 'POST'])
@login_required
def admin_add_flight():
    """Add a new flight"""
    if request.method == 'POST':
        flight = {
            'codigo': request.form.get('codigo', '').strip().upper(),
            'origem': request.form.get('origem', '').strip().upper(),
            'destino': request.form.get('destino', '').strip().upper(),
            'milhas': int(request.form.get('milhas', 0)),
            'preco': float(request.form.get('preco', 0)),
            'tipo_aeronave': request.form.get('tipo_aeronave', ''),
            'assentos': int(request.form.get('assentos', 0)),
            'assentos_disponiveis': int(request.form.get('assentos', 0)),
            'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        }
        
        flights = get_flights()
        
        # Check if flight code already exists
        if any(f['codigo'] == flight['codigo'] for f in flights):
            flash('Código de voo já existe.', 'danger')
            return render_template('admin/flight_form.html', flight=flight, action='add')
        
        flights.append(flight)
        save_flights(flights)
        
        flash(f'Voo {flight["codigo"]} cadastrado com sucesso!', 'success')
        return redirect(url_for('admin_flights'))
    
    return render_template('admin/flight_form.html', flight={}, action='add')


@app.route('/admin/flights/edit/<flight_code>', methods=['GET', 'POST'])
@login_required
def admin_edit_flight(flight_code):
    """Edit an existing flight"""
    flights = get_flights()
    flight = next((f for f in flights if f['codigo'] == flight_code), None)
    
    if not flight:
        flash('Voo não encontrado.', 'danger')
        return redirect(url_for('admin_flights'))
    
    if request.method == 'POST':
        original_seats = flight.get('assentos', 0)
        new_seats = int(request.form.get('assentos', 0))
        seats_diff = new_seats - original_seats
        
        flight['origem'] = request.form.get('origem', '').strip().upper()
        flight['destino'] = request.form.get('destino', '').strip().upper()
        flight['milhas'] = int(request.form.get('milhas', 0))
        flight['preco'] = float(request.form.get('preco', 0))
        flight['tipo_aeronave'] = request.form.get('tipo_aeronave', '')
        flight['assentos'] = new_seats
        flight['assentos_disponiveis'] = max(0, flight.get('assentos_disponiveis', 0) + seats_diff)
        
        save_flights(flights)
        
        flash(f'Voo {flight_code} atualizado com sucesso!', 'success')
        return redirect(url_for('admin_flights'))
    
    return render_template('admin/flight_form.html', flight=flight, action='edit')


@app.route('/admin/flights/delete/<flight_code>', methods=['POST'])
@login_required
def admin_delete_flight(flight_code):
    """Delete a flight"""
    flights = get_flights()
    flights = [f for f in flights if f['codigo'] != flight_code]
    save_flights(flights)
    
    flash(f'Voo {flight_code} excluído com sucesso!', 'success')
    return redirect(url_for('admin_flights'))


# Reservation Management
@app.route('/admin/reservations')
@login_required
def admin_reservations():
    """List all reservations"""
    reservations = get_reservations()
    return render_template('admin/reservations.html', reservations=reservations)


@app.route('/admin/reservations/<reservation_code>')
@login_required
def admin_reservation_details(reservation_code):
    """View reservation details"""
    reservations = get_reservations()
    reservation = reservations.get(reservation_code)
    
    if not reservation:
        flash('Reserva não encontrada.', 'danger')
        return redirect(url_for('admin_reservations'))
    
    flights = get_flights()
    flight_details = [f for f in flights if f['codigo'] in reservation.get('voos', [])]
    
    return render_template('admin/reservation_details.html',
                         reservation=reservation,
                         flights=flight_details)


# Client Management
@app.route('/admin/clients')
@login_required
def admin_clients():
    """List all clients"""
    btree = get_clients_btree()
    clients = btree.get_all_clients()
    
    # Sort options
    sort_by = request.args.get('sort', 'cpf')
    if sort_by == 'nome':
        clients.sort(key=lambda x: x.get('nome', ''))
    else:
        clients.sort(key=lambda x: x.get('cpf', ''))
    
    return render_template('admin/clients.html', clients=clients, sort_by=sort_by)


@app.route('/admin/clients/search', methods=['GET', 'POST'])
@login_required
def admin_search_clients():
    """Search clients"""
    if request.method == 'POST':
        search_type = request.form.get('search_type', 'cpf')
        search_value = request.form.get('search_value', '').strip()
        
        btree = get_clients_btree()
        
        if search_type == 'cpf':
            client = btree.search(search_value)
            clients = [client] if client else []
        elif search_type == 'nome':
            client = btree.search_by_name(search_value)
            clients = [client] if client else []
        elif search_type == 'inicial':
            clients = btree.search_by_initial(search_value)
        else:
            clients = []
        
        return render_template('admin/clients_search.html', 
                             clients=clients,
                             search_type=search_type,
                             search_value=search_value)
    
    return render_template('admin/clients_search.html', clients=None)


@app.route('/admin/clients/<cpf>')
@login_required
def admin_client_details(cpf):
    """View client details"""
    btree = get_clients_btree()
    client = btree.search(cpf)
    
    if not client:
        flash('Cliente não encontrado.', 'danger')
        return redirect(url_for('admin_clients'))
    
    # Get client's reservations
    reservations = get_reservations()
    client_reservations = [reservations[code] for code in client.get('reservas', []) if code in reservations]
    
    return render_template('admin/client_details.html',
                         client=client,
                         reservations=client_reservations)


# User Management
@app.route('/admin/users')
@admin_required
def admin_users():
    """List admin users"""
    users = get_users()
    return render_template('admin/users.html', users=users)


@app.route('/admin/users/add', methods=['GET', 'POST'])
@admin_required
def admin_add_user():
    """Add new admin user"""
    if request.method == 'POST':
        username = request.form.get('username', '').strip()
        password = request.form.get('password', '')
        name = request.form.get('name', '').strip()
        role = request.form.get('role', 'staff')
        
        if not username or not password:
            flash('Usuário e senha são obrigatórios.', 'danger')
            return render_template('admin/user_form.html', action='add')
        
        users = get_users()
        
        if username in users:
            flash('Nome de usuário já existe.', 'danger')
            return render_template('admin/user_form.html', action='add')
        
        users[username] = {
            'password': hashlib.sha256(password.encode()).hexdigest(),
            'role': role,
            'name': name or username
        }
        save_users(users)
        
        flash(f'Usuário {username} criado com sucesso!', 'success')
        return redirect(url_for('admin_users'))
    
    return render_template('admin/user_form.html', action='add')


# ============================================================================
# API ENDPOINTS
# ============================================================================

@app.route('/api/flights')
def api_flights():
    """API endpoint to get all flights"""
    flights = get_flights()
    return jsonify(flights)


@app.route('/api/search', methods=['POST'])
def api_search():
    """API endpoint to search flights"""
    data = request.get_json()
    origin = data.get('origin', '')
    destination = data.get('destination', '')
    
    graph = get_flight_graph()
    
    # Direct flights
    direct = graph.find_direct_flights(origin, destination)
    
    # Connections
    connections = graph.find_connections(origin, destination)
    
    return jsonify({
        'direct': [f for _, f in direct],
        'connections': connections
    })


# ============================================================================
# MAIN
# ============================================================================

if __name__ == '__main__':
    # Initialize default data if needed
    ensure_data_dir()
    get_users()  # Create default admin if not exists
    
    # Add sample flights if none exist
    flights = get_flights()
    if not flights:
        sample_flights = [
            {
                'codigo': 'ED001',
                'origem': 'GRU',
                'destino': 'GIG',
                'milhas': 450,
                'preco': 350.00,
                'tipo_aeronave': 'Boeing 737',
                'assentos': 180,
                'assentos_disponiveis': 180,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            },
            {
                'codigo': 'ED002',
                'origem': 'GIG',
                'destino': 'BSB',
                'milhas': 920,
                'preco': 520.00,
                'tipo_aeronave': 'Airbus A320',
                'assentos': 150,
                'assentos_disponiveis': 150,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            },
            {
                'codigo': 'ED003',
                'origem': 'GRU',
                'destino': 'BSB',
                'milhas': 870,
                'preco': 480.00,
                'tipo_aeronave': 'Boeing 737',
                'assentos': 180,
                'assentos_disponiveis': 180,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            },
            {
                'codigo': 'ED004',
                'origem': 'BSB',
                'destino': 'FOR',
                'milhas': 1680,
                'preco': 650.00,
                'tipo_aeronave': 'Airbus A320',
                'assentos': 150,
                'assentos_disponiveis': 150,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            },
            {
                'codigo': 'ED005',
                'origem': 'GRU',
                'destino': 'MIA',
                'milhas': 7200,
                'preco': 2800.00,
                'tipo_aeronave': 'Boeing 777',
                'assentos': 300,
                'assentos_disponiveis': 300,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            },
            {
                'codigo': 'ED006',
                'origem': 'GRU',
                'destino': 'LIS',
                'milhas': 8000,
                'preco': 3200.00,
                'tipo_aeronave': 'Airbus A350',
                'assentos': 280,
                'assentos_disponiveis': 280,
                'data_criacao': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
        ]
        save_flights(sample_flights)
    
    # Debug mode should only be enabled in development environments
    debug_mode = os.environ.get('FLASK_DEBUG', 'False').lower() == 'true'
    app.run(debug=debug_mode, host='0.0.0.0', port=5000)
