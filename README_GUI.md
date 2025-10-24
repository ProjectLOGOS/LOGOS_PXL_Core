# LOGOS AGI GUI System

A comprehensive graphical user interface for the LOGOS AGI cognitive reasoning system, featuring both desktop and web-based interfaces.

## 🚀 Quick Start

### 1. Setup Dependencies
```bash
python setup_gui.py
```

### 2. Start LOGOS Core Services
```bash
python deploy_core_services.py
```

### 3. Launch GUI
```bash
# Web Interface (Recommended)
python launch_gui.py --mode web

# Desktop Interface
python launch_gui.py --mode desktop

# Both Interfaces
python launch_gui.py --mode both
```

## 🌐 Web Interface

The web interface provides a modern, responsive GUI accessible from any browser.

### Features:
- **Real-time System Monitoring** - Live status updates via WebSocket
- **Falsifiability Validation** - Interactive countermodel generation
- **Reasoning Queries** - Natural language reasoning interface
- **Performance Analytics** - Visual charts and metrics
- **Mobile Responsive** - Works on desktop, tablet, and mobile
- **Session Management** - Persistent reasoning sessions

### Access:
- URL: `http://localhost:3001`
- No installation required on client devices
- Cross-platform compatibility

## 🖥️ Desktop Interface

The desktop interface provides a rich, native application experience using Tkinter.

### Features:
- **Tabbed Interface** - Organized workflow with multiple tabs
- **Advanced Visualizations** - Interactive charts and plots
- **Offline Capability** - Works without internet connection
- **Native Integration** - OS-level notifications and shortcuts
- **Performance Optimized** - Direct system resource access

### Tabs:
1. **Falsifiability** - Countermodel generation and validation
2. **Reasoning** - Query interface and results
3. **Monitor** - System status and health metrics
4. **Performance** - Analytics and performance charts
5. **Settings** - Configuration and preferences

## 📊 Core Features

### Falsifiability Framework
- **Countermodel Generation** - Systematic Kripke model construction
- **Modal Logic Validation** - Formal verification of safety properties
- **Safety Hooks** - Real-time safety constraint monitoring
- **Formal Proofs** - Mathematical verification support

### Reasoning Engine
- **Natural Language Queries** - Human-readable question interface
- **Logical Inference** - Formal reasoning and deduction
- **Knowledge Base** - Persistent fact storage and retrieval
- **Context Awareness** - Session-based reasoning context

### System Monitoring
- **Health Status** - Real-time service health monitoring
- **Performance Metrics** - CPU, memory, and response time tracking
- **Error Logging** - Comprehensive error tracking and reporting
- **Resource Usage** - System resource utilization monitoring

## 🔧 Configuration

### Environment Variables
```bash
LOGOS_API_URL=http://localhost:8090
LOGOS_WEB_PORT=3001
LOGOS_LOG_LEVEL=INFO
```

### Configuration Files
- `config/gui_settings.json` - GUI preferences
- `config/api_endpoints.json` - API endpoint configuration
- `config/display_settings.json` - Display and theme settings

## 🛠️ Development

### Project Structure
```
LOGOS_PXL_Core/
├── logos_gui.py           # Desktop GUI (Tkinter)
├── logos_web_gui.py       # Web GUI (FastAPI)
├── launch_gui.py          # GUI launcher utility
├── setup_gui.py           # Dependency installer
├── static/                # Web assets
│   ├── css/
│   ├── js/
│   └── images/
└── templates/             # HTML templates
    └── index.html
```

### Dependencies
- **Core**: FastAPI, Uvicorn, Tkinter
- **Visualization**: Matplotlib, Plotly, Chart.js
- **Data**: NumPy, Pandas
- **Communication**: WebSockets, Requests, Aiohttp
- **UI**: Jinja2, Bootstrap CSS

### API Integration
The GUI interfaces connect to the LOGOS API running on `localhost:8090`:

#### Key Endpoints:
- `GET /health` - System health status
- `POST /falsifiability/validate` - Falsifiability validation
- `POST /reasoning/query` - Reasoning queries
- `GET /monitor/status` - System monitoring
- `WebSocket /ws` - Real-time updates

## 🧪 Testing

### Manual Testing
```bash
# Test web interface
curl http://localhost:3001/health

# Test API connectivity
python -c "import requests; print(requests.get('http://localhost:8090/health').json())"
```

### Automated Testing
```bash
# Run GUI tests
python -m pytest tests/gui/

# Run integration tests
python tests/integration/test_gui_api.py
```

## 🔒 Security

### Authentication
- Session-based authentication for web interface
- Local-only access for desktop interface
- API key validation for external connections

### Data Protection
- HTTPS support for production deployments
- Input sanitization and validation
- Secure WebSocket connections

## 📱 Mobile Support

The web interface is fully responsive and optimized for mobile devices:
- Touch-friendly interface elements
- Adaptive layouts for various screen sizes
- Mobile-optimized navigation
- Offline capability with service workers

## 🐛 Troubleshooting

### Common Issues

#### GUI Won't Start
```bash
# Check dependencies
python setup_gui.py

# Verify API connection
python launch_gui.py --check-only
```

#### Web Interface Not Loading
- Ensure port 3001 is available
- Check firewall settings
- Verify LOGOS API is running on port 8090

#### Desktop GUI Crashes
- Update Tkinter: `pip install --upgrade tkinter`
- Check Python version compatibility (3.8+)
- Verify matplotlib installation

#### Performance Issues
- Monitor system resources
- Adjust refresh rates in settings
- Enable GPU acceleration for visualizations

### Log Files
- Web GUI: `logs/web_gui.log`
- Desktop GUI: `logs/desktop_gui.log`
- API Communication: `logs/api_client.log`

## 🔄 Updates

### Version Management
- GUI version: Check `__version__` in gui modules
- API compatibility: Automatic version checking
- Dependency updates: Run `setup_gui.py` periodically

### Feature Requests
Submit feature requests via the integrated feedback system in the GUI or create issues in the project repository.

## 📞 Support

For technical support and questions:
1. Check the troubleshooting section above
2. Review log files for error messages
3. Verify all dependencies are installed
4. Ensure LOGOS core services are running

## 🎯 Roadmap

### Upcoming Features
- [ ] Plugin system for custom visualizations
- [ ] Multi-language support
- [ ] Advanced theming options
- [ ] Export functionality for reasoning sessions
- [ ] Integration with external knowledge bases
- [ ] Voice interface support
- [ ] Collaborative reasoning sessions
- [ ] Cloud deployment options

---

*LOGOS AGI GUI System - Empowering Human-AI Collaboration Through Intuitive Interfaces*
